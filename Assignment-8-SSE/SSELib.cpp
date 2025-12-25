/**
 * SSELib.cpp
 * @author kisslune 
 */

#include "SSEHeader.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;

/// Traverses the ICFG to find paths from source to sink.
/// Uses DFS with a visited set (Edge + CallStack) to handle loops and recursion.
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
    
    // 1. Determine current node. If curEdge is null, we are at the start (src).
    const ICFGNode* currentNode = (curEdge == nullptr) ? 
                                  *(sources.begin()) : // Assuming single source for this context
                                  curEdge->getDstNode();

    // 2. Manage the current path vector
    if (curEdge != nullptr) {
        path.push_back(curEdge);
    }

    // 3. Check if we reached the sink (Assertion node)
    if (currentNode == snk) {
        collectAndTranslatePath();
    } 
    else {
        // 4. Traverse outgoing edges
        for (ICFGEdge* edge : currentNode->getOutEdges()) {
            // Context sensitivity check: Pair current edge with current callstack
            ICFGEdgeStackPair item = std::make_pair(edge, callstack);
            
            // Avoid cycles in the same calling context
            if (visited.find(item) == visited.end()) {
                visited.insert(item);
                reachability(edge, snk);
                visited.erase(item); // Backtrack
            }
        }
    }

    // 5. Backtrack path vector
    if (curEdge != nullptr) {
        path.pop_back();
    }
}

/// Collects the current path, translates it to Z3 constraints, and checks feasibility.
void SSE::collectAndTranslatePath() {
    // 1. Serialize path to string to check for uniqueness
    std::string pathStr = "";
    for (const ICFGEdge* edge : path) {
        pathStr += std::to_string(edge->getEdgeID()) + ",";
    }

    // 2. If path hasn't been processed yet
    if (paths.find(pathStr) == paths.end()) {
        paths.insert(pathStr);

        // 3. Reset solver before translating a new path to ensure clean state
        resetSolver();

        // 4. Translate path: Encode logic into Z3
        // If translatePath returns true, the path is mathematically feasible
        if (translatePath(path)) {
            // 5. Check the assertion at the end of the path
            const ICFGNode* lastNode = path.back()->getDstNode();
            assertchecking(lastNode);
        }
        
        // 6. Clean up solver after checking
        resetSolver();
    }
}

/// Handles Function Call: Maps actual parameters to formal parameters.
void SSE::handleCall(const CallCFGEdge* calledge) {
    const CallICFGNode* callNode = SVFUtil::dyn_cast<CallICFGNode>(calledge->getSrcNode());
    const FunEntryICFGNode* funEntry = SVFUtil::dyn_cast<FunEntryICFGNode>(calledge->getDstNode());
    
    // 1. Update Context
    pushCallingCtx(callNode);
    callstack.push_back(callNode);

    // 2. Map Arguments: Formal Param (in callee) == Actual Param (in caller)
    // Note: Use 'callingCtx' for actuals (caller context), 
    // but the formal params are new variables in the new scope.
    // However, getZ3Expr handles context internally usually, but for formals 
    // we need to ensure we are setting the value for the *new* context.
    
    // We are currently IN the caller context (before push) for the argument evaluation,
    // but we just pushed the context. We need to be careful.
    // Usually: Arg(caller) -> Param(callee)
    
    // Let's look at getZ3Expr. It uses `callingCtx`.
    // The Actual Param is evaluated in the *previous* context (before the push).
    // The Formal Param is evaluated in the *current* context (after the push).
    
    // To implement this simply with the provided API:
    // We assume the variable IDs are unique.
    
    u32_t argNum = callNode->getActualParmNum();
    for (u32_t i = 0; i < argNum; ++i) {
        const SVFVar* actual = callNode->getActualParm(i);
        const SVFVar* formal = funEntry->getFormalPar(i);
        
        // Get expression for Actual (Caller side)
        // Since we pushed context, we might need to pop to get actual's value correctly
        // if the Z3Mgr relies strictly on current `callingCtx`.
        // However, standard SVF SSE usually evaluates actuals *before* context switch.
        // Given the API `pushCallingCtx` is void and simply updates a vector, 
        // we can temporarily pop to get actual, then push back for formal.
        
        popCallingCtx(); 
        z3::expr actualExpr = getZ3Expr(actual->getId());
        pushCallingCtx(callNode);
        
        z3::expr formalExpr = getZ3Expr(formal->getId());
        
        addToSolver(formalExpr == actualExpr);
    }
}

/// Handles Function Return: Maps return value to call-site result.
void SSE::handleRet(const RetCFGEdge* retEdge) {
    const FunExitICFGNode* funExit = SVFUtil::dyn_cast<FunExitICFGNode>(retEdge->getSrcNode());
    const CallICFGNode* callNode = SVFUtil::dyn_cast<CallICFGNode>(retEdge->getDstNode());

    // 1. Handle Return Value logic if the function returns something
    if (funExit->isRetNode()) {
        const SVFVar* retVar = funExit->getRetVar();
        const SVFVar* resVar = callNode->getRetResVar(); // The variable receiving the result at callsite
        
        if (retVar && resVar) {
            z3::expr retExpr = getZ3Expr(retVar->getId()); // Callee context
            
            // We are about to return, so we pop context to get back to caller
            popCallingCtx(); 
            callstack.pop_back();
            
            z3::expr resExpr = getZ3Expr(resVar->getId()); // Caller context
            
            addToSolver(resExpr == retExpr);
        } else {
            // Void return or unused result, just pop
            popCallingCtx();
            callstack.pop_back();
        }
    } else {
        // No return value
        popCallingCtx();
        callstack.pop_back();
    }
}

/// Handles Branching: Adds path conditions to the solver.
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    // 1. Get the condition variable (e.g., %cmp)
    const SVFVar* condVar = edge->getCondition();
    
    if (condVar) {
        z3::expr condExpr = getZ3Expr(condVar->getId());
        
        // 2. Get the value required to take this branch (0 or 1)
        u32_t successValue = edge->getSuccessorCondValue();
        
        // 3. Add constraint: ConditionVar == BranchValue
        addToSolver(condExpr == getCtx().int_val(successValue));
        
        // 4. Check feasibility
        if (getSolver().check() == z3::unsat) {
            return false;
        }
    }
    return true;
}

/// Handles Standard Statements (Memory, Copy, CMP, etc.)
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
    const ICFGNode* dstNode = edge->getDstNode();
    const ICFGNode* srcNode = edge->getSrcNode(); // Used for Phi check
    
    DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            // p = &x
            // LHS = Address(RHS)
            z3::expr lhs = getZ3Expr(addr->getLHSVarID());
            z3::expr rhsAddr = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == rhsAddr);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // x = y
            z3::expr lhs = getZ3Expr(copy->getLHSVarID());
            z3::expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // x = *p
            // LHS = Load(RHS)
            z3::expr lhs = getZ3Expr(load->getLHSVarID());
            z3::expr rhsPtr = getZ3Expr(load->getRHSVarID());
            
            // Ensure pointer is valid before loading (optional but good for debugging)
            // But here we just construct the constraint
            z3::expr loadedVal = z3Mgr->loadValue(rhsPtr);
            addToSolver(lhs == loadedVal);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // *p = y
            // Store(LHS, RHS) -> Updates global memory state
            z3::expr ptr = getZ3Expr(store->getLHSVarID());
            z3::expr val = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(ptr, val);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // p = &base[offset]
            z3::expr lhs = getZ3Expr(gep->getLHSVarID());
            z3::expr base = getZ3Expr(gep->getBaseVarID());
            
            // Calculate offset using Z3Mgr helper
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            
            // Get new address
            z3::expr newAddr = z3Mgr->getGepObjAddress(base, offset);
            addToSolver(lhs == newAddr);
        }
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            z3::expr res = getZ3Expr(cmp->getResID());
            z3::expr op0 = getZ3Expr(cmp->getOpVarID(0));
            z3::expr op1 = getZ3Expr(cmp->getOpVarID(1));
            
            z3::expr cond(getCtx());
            
            // Handle integer predicates
            switch(cmp->getPredicate()) {
                case CmpStmt::ICMP_EQ:  cond = (op0 == op1); break;
                case CmpStmt::ICMP_NE:  cond = (op0 != op1); break;
                case CmpStmt::ICMP_SGT: cond = (op0 > op1); break;
                case CmpStmt::ICMP_SGE: cond = (op0 >= op1); break;
                case CmpStmt::ICMP_SLT: cond = (op0 < op1); break;
                case CmpStmt::ICMP_SLE: cond = (op0 <= op1); break;
                // Treat Unsigned same as Signed for basic integer assignment context 
                // unless bitvector explicit handling is required (simple Z3 Int sort handles mathematical comparison)
                case CmpStmt::ICMP_UGT: cond = (op0 > op1); break; 
                case CmpStmt::ICMP_UGE: cond = (op0 >= op1); break;
                case CmpStmt::ICMP_ULT: cond = (op0 < op1); break;
                case CmpStmt::ICMP_ULE: cond = (op0 <= op1); break;
                default: cond = (op0 == op1); break; // Fallback
            }
            
            // Convert boolean condition to integer (1 or 0) for the result variable
            // res = (cond) ? 1 : 0
            addToSolver(res == z3::ite(cond, getCtx().int_val(1), getCtx().int_val(0)));
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
             // ... existing BinaryOPStmt implementation in provided code ...
             // You can copy the BinaryOPStmt block from your provided text here if needed, 
             // but based on the prompt, it seemed partially implemented. 
             // I will leave the structure consistent with your provided file 
             // assuming the rest of BinaryOPStmt is already there or handled.
             
             // Re-inserting the BinaryOP logic for completeness if it was part of the TODO block logic:
             expr op0 = getZ3Expr(binary->getOpVarID(0));
             expr op1 = getZ3Expr(binary->getOpVarID(1));
             expr res = getZ3Expr(binary->getResID());
             switch (binary->getOpcode())
             {
                case BinaryOperator::Add: addToSolver(res == op0 + op1); break;
                case BinaryOperator::Sub: addToSolver(res == op0 - op1); break;
                case BinaryOperator::Mul: addToSolver(res == op0 * op1); break;
                case BinaryOperator::SDiv: addToSolver(res == op0 / op1); break;
                case BinaryOperator::SRem: addToSolver(res == op0 % op1); break;
                // Bitwise operations require conversion to BitVectors if variables are Ints
                case BinaryOperator::Xor: addToSolver(res == bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1)); break;
                case BinaryOperator::And: addToSolver(res == bv2int(int2bv(32, op0) & int2bv(32, op1), 1)); break;
                case BinaryOperator::Or:  addToSolver(res == bv2int(int2bv(32, op0) | int2bv(32, op1), 1)); break;
                case BinaryOperator::AShr: addToSolver(res == bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1)); break;
                case BinaryOperator::Shl:  addToSolver(res == bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1)); break;
                default: break;
             }
        }
        else if (const BranchStmt *br = SVFUtil::dyn_cast<BranchStmt>(stmt))
        {
            DBOP(std::cout << "\t skip handled when traversal Conditional IntraCFGEdge \n");
        }
        else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt)) {
            expr res = getZ3Expr(select->getResID());
            expr tval = getZ3Expr(select->getTrueValue()->getId());
            expr fval = getZ3Expr(select->getFalseValue()->getId());
            expr cond = getZ3Expr(select->getCondition()->getId());
            addToSolver(res == ite(cond == getCtx().int_val(1), tval, fval));
        }
        else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt)) {
            expr res = getZ3Expr(phi->getResID());
            bool opINodeFound = false;
            for(u32_t i = 0; i < phi->getOpVarNum(); i++){
                // Check if the source of the edge (predecessor) corresponds to this Phi operand's path
                if (srcNode && srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
                {
                    expr ope = getZ3Expr(phi->getOpVar(i)->getId());
                    addToSolver(res == ope);
                    opINodeFound = true;
                }
            }
        }
    }

    return true;
}
