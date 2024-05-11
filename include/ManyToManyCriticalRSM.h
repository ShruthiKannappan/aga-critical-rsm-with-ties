#ifndef MANY_TO_MANY_CRITICAL_RSM_H
#define MANY_TO_MANY_CRITICAL_RSM_H

#include "MatchingAlgorithm.h"

// Critical relaxed stable matching is critical as well as relaxed stable
// A matching M is critical if there is no other matching that matches 
// more critical vertices than M
// A matching M is relaxed stable if for every blocking pair (a, b) 
// w.r.t. M one of the following holds:
// 1. a is matched and b' = M(a) is critical, or
// 2. b is matched and a′ = M(b) is critical
class ManyToManyCriticalRSM : public MatchingAlgorithm {
private:
    void ties_propose(FreeListType& free_list, VertexPtr a, const PreferenceList& a_pref_list, std::map<VertexPtr, VertexBookkeeping>& bookkeep_data, Matching& M, std::unordered_map<VertexPtr, std::vector<VertexPtr>> &t_star_partners,const int t, std::unordered_map<VertexPtr,std::vector<VertexPtr>> &proposed_vertices);
    void critical_propose(FreeListType& free_list, const VertexPtr a, const VertexPtr b,int q_a,int q_b, std::map<VertexPtr, VertexBookkeeping>& bookkeep_data, Matching& M,std::unordered_map<VertexPtr, std::vector<VertexPtr>> &t_star_partners);

public:
    VertexPtr favourite_neighbour(VertexPtr u, const PreferenceList& u_pref_list, VertexBookkeeping &u_data, const Matching& M, std::unordered_map<VertexPtr,std::vector<VertexPtr>> proposed_vertices);
    explicit ManyToManyCriticalRSM(std::shared_ptr<BipartiteGraph> G, bool A_proposing=true);
    ~ManyToManyCriticalRSM() override = default;

    bool verify(Matching &M) const;

    Matching compute_matching() override;
};

#endif

