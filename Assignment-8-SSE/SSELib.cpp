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
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
    const ICFGNode* currentNode = (curEdge == nullptr) ? 
                                  *(sources.begin()) : 
                                  curEdge->getDstNode();

    if (curEdge != nullptr) {
        path.push_back(curEdge);
    }

    if (currentNode == snk) {
        collectAndTranslatePath();
    } 
    else {
        for (ICFGEdge* edge : currentNode->getOutEdges()) {
            ICFGEdgeStackPair item = std::make_pair(edge, callstack);
            if (visited.find(item) == visited.end()) {
                visited.insert(item);
                reachability(edge, snk);
                visited.erase(item);
            }
        }
    }

    if (curEdge != nullptr) {
        path.pop_back();
    }
}

/// Collects the current path, translates it to Z3 constraints, and checks feasibility.
void SSE::collectAndTranslatePath() {
    std::string pathStr = "";
    for (const ICFGEdge* edge : path) {
        // Fix: getEdgeID() does not exist. Construct ID from Src and Dst IDs.
        pathStr += std::to_string(edge->getSrcID()) + "_" + std::to_string(edge->getDstID()) + ",";
    }

    if (paths.find(pathStr) == paths.end()) {
        paths.insert(pathStr);
        resetSolver();

        if (translatePath(path)) {
            const ICFGNode* lastNode = path.back()->getDstNode();
            assertchecking(lastNode);
        }
        resetSolver();
    }
}

/// Handles Function Call: Maps actual parameters to formal parameters.
void SSE::handleCall(const CallCFGEdge* calledge) {
    const CallICFGNode* callNode = SVFUtil::dyn_cast<CallICFGNode>(calledge->getSrcNode());
    const FunEntryICFGNode* funEntry = SVFUtil::dyn_cast<FunEntryICFGNode>(calledge->getDstNode());
    
    pushCallingCtx(callNode);
    callstack.push_back(callNode);

    // Fix: Use getActualParms() vector size and indexing
    u32_t argNum = callNode->getActualParms().size();
    for (u32_t i = 0; i < argNum; ++i) {
        const SVFVar* actual = callNode->getActualParms()[i];
        const SVFVar* formal = funEntry->getFormalParms()[i];
        
        // Evaluate actual in caller context
        popCallingCtx(); 
        z3::expr actualExpr = getZ3Expr(actual->getId());
        pushCallingCtx(callNode);
        
        // Formal in callee context
        z3::expr formalExpr = getZ3Expr(formal->getId());
        
        addToSolver(formalExpr == actualExpr);
    }
}

/// Handles Function Return: Maps return value to call-site result.
void SSE::handleRet(const RetCFGEdge* retEdge) {
    const ICFGNode* srcNode = retEdge->getSrcNode(); // FunExit
    const ICFGNode* dstNode = retEdge->getDstNode(); // CallSite (or node containing CallStmt)

    const SVFVar* retVar = nullptr;
    const SVFVar* resVar = nullptr;

    // Fix: Traverse statements to find RetStmt and CallStmt since helper methods are missing
    
    // 1. Find the Return Value in the Function Exit Node (Callee)
    for (const SVFStmt* stmt : srcNode->getSVFStmts()) {
        if (const RetStmt* ret = SVFUtil::dyn_cast<RetStmt>(stmt)) {
            if (ret->getOpVarNum() > 0) {
                retVar = svfir->getGNode(ret->getOpVarID());
                break;
            }
        }
    }

    // 2. Find the Result Variable in the Call Site Node (Caller)
    for (const SVFStmt* stmt : dstNode->getSVFStmts()) {
        if (const CallStmt* call = SVFUtil::dyn_cast<CallStmt>(stmt)) {
            // Check if call has a return value assigned (LHS)
            // Note: getLHSVarID() returns the ID of the variable receiving the result
            resVar = svfir->getGNode(call->getLHSVarID());
            break;
        }
    }

    // Handle Contexts and Constraints
    if (retVar && resVar) {
        // RetVar is in Callee context (current context)
        z3::expr retExpr = getZ3Expr(retVar->getId());
        
        // Return to Caller context
        popCallingCtx();
        callstack.pop_back();
        
        // ResVar is in Caller context
        z3::expr resExpr = getZ3Expr(resVar->getId());
        
        addToSolver(resExpr == retExpr);
    } else {
        // Void return or analysis failed, just pop context
        popCallingCtx();
        callstack.pop_back();
    }
}

/// Handles Branching: Adds path conditions to the solver.
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    const SVFVar* condVar = edge->getCondition();
    
    if (condVar) {
        z3::expr condExpr = getZ3Expr(condVar->getId());
        u32_t successValue = edge->getSuccessorCondValue();
        addToSolver(condExpr == getCtx().int_val(successValue));
        
        if (getSolver().check() == z3::unsat) {
            return false;
        }
    }
    return true;
}

/// Handles Standard Statements
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
    const ICFGNode* dstNode = edge->getDstNode();
    const ICFGNode* srcNode = edge->getSrcNode(); 
    
    DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            z3::expr lhs = getZ3Expr(addr->getLHSVarID());
            z3::expr rhsAddr = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == rhsAddr);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            z3::expr lhs = getZ3Expr(copy->getLHSVarID());
            z3::expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            z3::expr lhs = getZ3Expr(load->getLHSVarID());
            z3::expr rhsPtr = getZ3Expr(load->getRHSVarID());
            z3::expr loadedVal = z3Mgr->loadValue(rhsPtr);
            addToSolver(lhs == loadedVal);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            z3::expr ptr = getZ3Expr(store->getLHSVarID());
            z3::expr val = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(ptr, val);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            z3::expr lhs = getZ3Expr(gep->getLHSVarID());
            // Fix: Use getRHSVarID() for the base pointer instead of getBaseVarID()
            z3::expr base = getZ3Expr(gep->getRHSVarID()); 
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            z3::expr newAddr = z3Mgr->getGepObjAddress(base, offset);
            addToSolver(lhs == newAddr);
        }
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            z3::expr res = getZ3Expr(cmp->getResID());
            z3::expr op0 = getZ3Expr(cmp->getOpVarID(0));
            z3::expr op1 = getZ3Expr(cmp->getOpVarID(1));
            z3::expr cond(getCtx());
            
            switch(cmp->getPredicate()) {
                case CmpStmt::ICMP_EQ:  cond = (op0 == op1); break;
                case CmpStmt::ICMP_NE:  cond = (op0 != op1); break;
                case CmpStmt::ICMP_SGT: cond = (op0 > op1); break;
                case CmpStmt::ICMP_SGE: cond = (op0 >= op1); break;
                case CmpStmt::ICMP_SLT: cond = (op0 < op1); break;
                case CmpStmt::ICMP_SLE: cond = (op0 <= op1); break;
                case CmpStmt::ICMP_UGT: cond = (op0 > op1); break; 
                case CmpStmt::ICMP_UGE: cond = (op0 >= op1); break;
                case CmpStmt::ICMP_ULT: cond = (op0 < op1); break;
                case CmpStmt::ICMP_ULE: cond = (op0 <= op1); break;
                default: cond = (op0 == op1); break;
            }
            addToSolver(res == z3::ite(cond, getCtx().int_val(1), getCtx().int_val(0)));
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
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
            for(u32_t i = 0; i < phi->getOpVarNum(); i++){
                if (srcNode && srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
                {
                    expr ope = getZ3Expr(phi->getOpVar(i)->getId());
                    addToSolver(res == ope);
                }
            }
        }
    }

    return true;
}
