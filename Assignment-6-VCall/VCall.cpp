/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A6Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
        OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                 "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);
    auto cg = pag->getCallGraph();

    // TODO: complete the following two methods
    andersen.runPointerAnalysis();
    andersen.updateCallGraph(cg);

    cg->dump();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}

void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    WorkList<unsigned> workList;

    for (auto it = consg->begin(); it != consg->end(); it++)
    {
        auto p = it->first;
        SVF::ConstraintNode *node = it->second;

        for (auto edge : node->getAddrInEdges())
        {
            SVF::AddrCGEdge *addrEdge = SVF::SVFUtil::dyn_cast<SVF::AddrCGEdge>(edge);
            auto srcId = addrEdge->getSrcID();
            auto dstId = addrEdge->getDstID();

            pts[dstId].insert(srcId);
            workList.push(dstId);
        }
    }

    while (!workList.empty())
    {
        auto p = workList.pop();
        SVF::ConstraintNode *pNode = consg->getConstraintNode(p);

        // for each o ∈ pts(p)
        for (auto o : pts[p])
        {
            // for each q --Store--> p
            for (auto edge : pNode->getStoreInEdges())
            {
                SVF::StoreCGEdge *storeEdge = SVF::SVFUtil::dyn_cast<SVF::StoreCGEdge>(edge);
                auto q = storeEdge->getSrcID();

                // q --Copy--> o exist?
                bool exist = false;
                SVF::ConstraintNode *qNode = consg->getConstraintNode(q);
                for (auto copyEdge : qNode->getCopyOutEdges())
                {
                    if (copyEdge->getDstID() == o)
                    {
                        exist = true;
                        break;
                    }
                }

                if (!exist)
                {
                    consg->addCopyCGEdge(q, o);
                    workList.push(q);
                }
            }

            // for each p --Load--> r
            for (auto edge : pNode->getLoadOutEdges())
            {
                SVF::LoadCGEdge *loadEdge = SVF::SVFUtil::dyn_cast<SVF::LoadCGEdge>(edge);
                auto r = loadEdge->getDstID();

                // o --Copy--> r exist?
                bool exist = false;
                SVF::ConstraintNode *rNode = consg->getConstraintNode(r);
                for (auto copyEdge : rNode->getCopyInEdges())
                {
                    if (copyEdge->getSrcID() == o)
                    {
                        exist = true;
                        break;
                    }
                }

                if (!exist)
                {
                    consg->addCopyCGEdge(o, r);
                    workList.push(o);
                }
            }
        }

        // for each p --Copy--> x
        for (auto edge : pNode->getCopyOutEdges())
        {
            SVF::CopyCGEdge *copyEdge = SVF::SVFUtil::dyn_cast<SVF::CopyCGEdge>(edge);
            auto x = copyEdge->getDstID();

            auto oldSize = pts[x].size();
            pts[x].insert(pts[p].begin(), pts[p].end());

            // pts(x) changed?
            if (pts[x].size() != oldSize)
            {
                workList.push(x);
            }
        }

        // for each p --Gep.fld--> x
        for (auto edge : pNode->getGepOutEdges())
        {
            SVF::GepCGEdge *gepEdge = SVF::SVFUtil::dyn_cast<SVF::GepCGEdge>(edge);
            auto x = gepEdge->getDstID();

            auto oldSize = pts[x].size();
            for (auto o : pts[p])
            {
                auto fieldObj = consg->getGepObjVar(o, gepEdge);
                pts[x].insert(fieldObj);
            }

            // pts(x) changed?
            if (pts[x].size() != oldSize)
            {
                workList.push(x);
            }
        }
    }
}

void Andersen::updateCallGraph(SVF::CallGraph *cg)
{
    // TODO: complete this method.
    //  The implementation of call graph is provided in the SVF library
    const auto &indirectCallsites = consg->getIndirectCallsites();

    for (const auto &callsitePair : indirectCallsites)
    {
        auto callNode = callsitePair.first;
        auto funPtrId = callsitePair.second;

        auto callerFun = callNode->getCaller();

        const auto &pointsToSet = pts[funPtrId];

        for (auto calleeId : pointsToSet)
        {
            if (consg->isFunction(calleeId))
            {
                auto calleeFun = consg->getFunction(calleeId);

                cg->addIndirectCallGraphEdge(callNode, callerFun, calleeFun);
            }
        }
    }
}
