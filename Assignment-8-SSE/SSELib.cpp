/**
 * SSELib.cpp
 * @author kisslune 
 */

#include "SSEHeader.h"
#include "Util/Options.h"
// 必须包含以下头文件以支持 SVF 语句类的具体定义
#include "SVFIR/SVFIR.h"
#include "SVFIR/SVFStatements.h"

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;

/// Traverses the ICFG to find paths from source to sink.
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
    // 1. 确定当前节点：如果是起始调用(curEdge为null)，则从源点开始；否则取边的目标节点
    const ICFGNode* currentNode = (curEdge == nullptr) ? 
                                  *(sources.begin()) : 
                                  curEdge->getDstNode();

    // 2. 将当前边加入路径
    if (curEdge != nullptr) {
        path.push_back(curEdge);
    }

    // 3. 判断是否到达汇点(Assertion)
    if (currentNode == snk) {
        collectAndTranslatePath();
    } 
    else {
        // 4. DFS 遍历：使用 visited 集合防止死循环，同时支持上下文敏感
        // visited 的 key 是 (Edge, CallStack)，确保同一调用上下文下不重复访问同一条边
        for (ICFGEdge* edge : currentNode->getOutEdges()) {
            ICFGEdgeStackPair item = std::make_pair(edge, callstack);
            
            if (visited.find(item) == visited.end()) {
                visited.insert(item);
                reachability(edge, snk); // 递归
                visited.erase(item);     // 回溯
            }
        }
    }

    // 5. 回溯：将当前边从路径中移除
    if (curEdge != nullptr) {
        path.pop_back();
    }
}

/// Collects the current path, translates it to Z3 constraints, and checks feasibility.
void SSE::collectAndTranslatePath() {
    // 1. 构建唯一的路径标识符字符串
    std::string pathStr = "";
    for (const ICFGEdge* edge : path) {
        pathStr += std::to_string(edge->getSrcID()) + "_" + std::to_string(edge->getDstID()) + ",";
    }

    // 2. 如果该路径未被处理过
    if (paths.find(pathStr) == paths.end()) {
        paths.insert(pathStr);
        
        // 3. 重置求解器状态
        resetSolver();

        // 4. 翻译路径约束。如果路径逻辑可行(translatePath返回true)
        if (translatePath(path)) {
            // 5. 验证路径末端的 Assertion
            const ICFGNode* lastNode = path.back()->getDstNode();
            assertchecking(lastNode);
        }
        
        // 6. 清理求解器
        resetSolver();
    }
}

/// Handles Function Call: Maps actual parameters to formal parameters.
void SSE::handleCall(const CallCFGEdge* calledge) {
    const CallICFGNode* callNode = SVFUtil::dyn_cast<CallICFGNode>(calledge->getSrcNode());
    const FunEntryICFGNode* funEntry = SVFUtil::dyn_cast<FunEntryICFGNode>(calledge->getDstNode());
    
    // 1. 更新调用上下文
    pushCallingCtx(callNode);
    callstack.push_back(callNode);

    // 2. 参数传递：形参(Formal) = 实参(Actual)
    u32_t argNum = callNode->getActualParms().size();
    for (u32_t i = 0; i < argNum; ++i) {
        const SVFVar* actual = callNode->getActualParms()[i];
        const SVFVar* formal = funEntry->getFormalParms()[i];
        
        // 关键：实参是在调用者(Caller)上下文中求值的
        popCallingCtx(); // 临时切回 Caller 上下文
        z3::expr actualExpr = getZ3Expr(actual->getId());
        pushCallingCtx(callNode); // 切回 Callee 上下文
        
        // 形参是在被调用者(Callee)上下文中
        z3::expr formalExpr = getZ3Expr(formal->getId());
        
        // 添加约束
        addToSolver(formalExpr == actualExpr);
    }
}

/// Handles Function Return: Maps return value to call-site result.
void SSE::handleRet(const RetCFGEdge* retEdge) {
    const ICFGNode* srcNode = retEdge->getSrcNode(); // FunExit Node
    const ICFGNode* dstNode = retEdge->getDstNode(); // CallSite Node

    const SVFVar* retVar = nullptr;
    const SVFVar* resVar = nullptr;

    // 1. 在 FunExit 节点中寻找 RetStmt (获取返回值)
    for (const SVFStmt* stmt : srcNode->getSVFStmts()) {
        if (const RetStmt* ret = SVFUtil::dyn_cast<RetStmt>(stmt)) {
            if (ret->getOpVarNum() > 0) {
                retVar = svfir->getGNode(ret->getOpVarID());
                break;
            }
        }
    }

    // 2. 在 CallSite 节点中寻找 CallStmt (获取接收返回值的变量)
    for (const SVFStmt* stmt : dstNode->getSVFStmts()) {
        if (const CallStmt* call = SVFUtil::dyn_cast<CallStmt>(stmt)) {
            resVar = svfir->getGNode(call->getLHSVarID());
            break;
        }
    }

    // 3. 处理返回值约束
    if (retVar && resVar) {
        // retVar 在当前(Callee)上下文
        z3::expr retExpr = getZ3Expr(retVar->getId());
        
        // 恢复到 Caller 上下文
        popCallingCtx();
        callstack.pop_back();
        
        // resVar 在 Caller 上下文
        z3::expr resExpr = getZ3Expr(resVar->getId());
        
        addToSolver(resExpr == retExpr);
    } else {
        // 无返回值或未找到，仅恢复上下文
        popCallingCtx();
        callstack.pop_back();
    }
}

/// Handles Branching: Adds path conditions to the solver.
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    const SVFVar* condVar = edge->getCondition();
    
    if (condVar) {
        z3::expr condExpr = getZ3Expr(condVar->getId());
        // 获取分支条件期望的值 (0 或 1)
        u32_t successValue = edge->getSuccessorCondValue();
        
        // 添加约束: 条件变量 == 期望值
        addToSolver(condExpr == getCtx().int_val(successValue));
        
        // 立即检查路径可行性，若不可行则停止该路径分析
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
            // LHS = &RHS
            z3::expr lhs = getZ3Expr(addr->getLHSVarID());
            z3::expr rhsAddr = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == rhsAddr);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // LHS = RHS
            z3::expr lhs = getZ3Expr(copy->getLHSVarID());
            z3::expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // LHS = *RHS
            z3::expr lhs = getZ3Expr(load->getLHSVarID());
            z3::expr rhsPtr = getZ3Expr(load->getRHSVarID());
            z3::expr loadedVal = z3Mgr->loadValue(rhsPtr);
            addToSolver(lhs == loadedVal);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // *LHS = RHS
            z3::expr ptr = getZ3Expr(store->getLHSVarID());
            z3::expr val = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(ptr, val);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // LHS = &Base[Offset]
            z3::expr lhs = getZ3Expr(gep->getLHSVarID());
            // 注意：GEP 的 Base 指针通常在 RHS 中
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
            
            // 处理各种比较谓词
            switch(cmp->getPredicate()) {
                case CmpStmt::ICMP_EQ:  cond = (op0 == op1); break;
                case CmpStmt::ICMP_NE:  cond = (op0 != op1); break;
                case CmpStmt::ICMP_SGT: cond = (op0 > op1); break;
                case CmpStmt::ICMP_SGE: cond = (op0 >= op1); break;
                case CmpStmt::ICMP_SLT: cond = (op0 < op1); break;
                case CmpStmt::ICMP_SLE: cond = (op0 <= op1); break;
                // 无符号比较在 Z3 Int 模式下通常可按有符号处理，除非涉及位向量溢出
                case CmpStmt::ICMP_UGT: cond = (op0 > op1); break; 
                case CmpStmt::ICMP_UGE: cond = (op0 >= op1); break;
                case CmpStmt::ICMP_ULT: cond = (op0 < op1); break;
                case CmpStmt::ICMP_ULE: cond = (op0 <= op1); break;
                default: cond = (op0 == op1); break;
            }
            // 将布尔结果转换为整数 (1 或 0)
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
                // 位运算需要转换为 BitVector
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
                // 仅处理来自实际执行路径前驱节点的 Phi 操作数
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
