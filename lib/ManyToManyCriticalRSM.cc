#include "ManyToManyCriticalRSM.h"
#include "MatchingAlgorithm.h"
#include "VertexBookkeeping.h"
#include "Utils.h"
#include "Vertex.h"
#include <iostream>
#include <algorithm>

ManyToManyCriticalRSM::ManyToManyCriticalRSM(std::shared_ptr<BipartiteGraph> G, bool A_proposing)
    : MatchingAlgorithm(G, A_proposing)
{}

Matching ManyToManyCriticalRSM::compute_matching() {
  FreeListType free_list;
  std::map<VertexPtr, VertexBookkeeping> bookkeep_data;
  std::shared_ptr<BipartiteGraph> G = get_graph();
  auto M = Matching(is_A_proposing());

  // choose the partitions from which the vertices will propose
  const auto& proposing_partition = is_A_proposing() ? G->get_A_partition()
                                                     : G->get_B_partition();

  const auto& non_proposing_partition = is_A_proposing() ? G->get_B_partition()
                                                         : G->get_A_partition();

  // s is sum of lower quotas of proposing vertices.
  auto s = 0;
  for (const auto& [_, v] : proposing_partition) {
    s += v->get_lower_quota();
  }

  // t is sum of lower quotas of non-proposing vertices.
  auto t = 0;
  for (const auto& [_, v] : non_proposing_partition) {
    t += v->get_lower_quota();
  }

  // set the level of every vertex in the proposing partition to 0
  // mark all proposing vertices free (by pushing into the free_list)
  // and vertices from the opposite partition implicitly free
  // A side
  for (const auto& [_, v] : proposing_partition) {
    int pref_list_size = v->get_preference_list().size();
    int pref_list_lq_size = v->get_preference_list_lq().size();
    auto vertex_data{VertexBookkeeping(0, pref_list_size,
                                       0, pref_list_lq_size)};// constructor not clear do go through the initial values
    
    vertex_data.residual = v->get_upper_quota();
    vertex_data.star = false;
    vertex_data.level = 0;
    bookkeep_data[v] = vertex_data;
    free_list.push(v);
  }
  // setting capacity of b in B as residual in BookKeeping Data
  for (const auto& [_, v] : non_proposing_partition) {
    auto vertex_data{VertexBookkeeping()};
    vertex_data.residual = v->get_lower_quota();
    bookkeep_data[v] = vertex_data;
  }
  // Make prefSC and prefS for each vertex
  std::unordered_map<VertexPtr, PreferenceList> prefS;
  std::unordered_map<VertexPtr, PreferenceList> prefSLQ;
  std::unordered_map<VertexPtr, RankType> prefS_proposal_index;
  std::unordered_map<VertexPtr, RankType> prefSLQ_proposal_index;
  // t_star_partners returns the partners of b that are matched to it at t* level.
  std::unordered_map<VertexPtr, std::vector<VertexPtr>> t_star_partners;
  // map for vertices in A, to a vector of vertices that they have already proposed to at the current level.
  std::unordered_map<VertexPtr,std::vector<VertexPtr>> proposed_vertices;

  //initializing prefs, prefslq and their proposing indices  
  for (auto &it: proposing_partition) {
    auto a = it.second;
    auto pref_list_a = a->get_preference_list();
    prefS[a] = pref_list_a.get_prefS();
    prefSLQ[a] = pref_list_a.get_prefSC();
    prefS_proposal_index[a] = 0;
    prefSLQ_proposal_index[a] = 0;
  }
  

  while(!free_list.empty())
  {
      //dequeue a^l
      
      auto a = remove_from_free_list(free_list, bookkeep_data);
      auto &a_pref_list = a->get_preference_list();
      auto &a_data = bookkeep_data[a];
      auto l = a_data.level;
      bool star = a_data.star;
    
      if(l<t)
      {
        
        if (prefSLQ_proposal_index[a] < prefSLQ[a].size()) // checking a^l has exhausted PrefSLQ 
        {
          auto b_partner = prefSLQ[a].at(prefSLQ_proposal_index[a]); // b = most preferred unproposed vertex by a
          auto b  = b_partner.vertex;
          critical_propose(free_list,a,b,a->get_upper_quota(),b->get_lower_quota(),bookkeep_data,M,t_star_partners);
          prefSLQ_proposal_index[a] += 1;
          proposed_vertices[a].push_back(b);
        }
        else// incrementing the level after exhaustion of prefslq
        {
          bookkeep_data[a].level++;
          prefSLQ_proposal_index[a] = 0;
          proposed_vertices[a].clear();
          add_to_free_list(free_list, bookkeep_data[a],a);
        }
      }
      else if(l==t)
      {
        if(a_data.begin<a_data.end)
        {
          ties_propose(free_list,a,a_pref_list,bookkeep_data,M,t_star_partners,t,proposed_vertices);
        }
        else
        {
          if(!a_data.star)
          {
            a_data.star = true;
            a_data.begin = 0;
            a_data.tied_index = 0;
            proposed_vertices[a].clear();
          }
          else
          {
            if(M.number_of_partners(a)<a->get_lower_quota())
            {
              a_data.level = t+1;
              a_data.begin = 0;
              a_data.star = false;
              proposed_vertices[a].clear();
              add_to_free_list(free_list, bookkeep_data[a],a);
            }
          }
        }
      }
      else 
      {
        if (prefS_proposal_index[a] < prefS[a].size()) //checking if a^l has exhausted prefs 
        {
          auto b_partner = prefS[a].at(prefS_proposal_index[a]);
          auto b  = b_partner.vertex;
          //updating the capacity of b
          if(M.is_matched_lt(b,t))
          {
            bookkeep_data[b].residual = b->get_lower_quota();
          }
          else
          {
            bookkeep_data[b].residual = b->get_upper_quota();
          }
          critical_propose(free_list,a,b,a->get_lower_quota(),bookkeep_data[b].residual,bookkeep_data,M,t_star_partners);
          prefS_proposal_index[a] += 1;
          proposed_vertices[a].push_back(b);
        }
        else
        {
          // incrementing the level if a is still lower quota after exhaustion of prefs
          if(l<s+t && M.number_of_partners(a) <(a->get_lower_quota())) 
          {
            bookkeep_data[a].level++;
            prefS_proposal_index[a] = 0;
            proposed_vertices[a].clear();
            add_to_free_list(free_list, bookkeep_data[a],a);
          }
        }   
      }

  }
  return M;
}

bool check_blocking_pair(VertexPtr a , VertexPtr b , Matching & M) 
{
  // checking if a is either undersubscribed or has a b_prime as its neighbour
  // which is lesser preferred than b in M
  bool check_a_blocking = M.number_of_partners(a) < a->get_upper_quota();
  auto matched_partners_a = M.get_partners(a);
  for(auto & partner : matched_partners_a ){
    auto b_prime = partner.vertex ;
    if(a->get_preference_list().prefers(b,b_prime)==cBetter){
      check_a_blocking = true ;
      break ;
    }
  }

  // checking if b is either undersubscribed or has a a_prime as its neighbour
  // which is lesser preferred than a in M
  bool check_b_blocking = M.number_of_partners(b) < b->get_upper_quota();
  auto matched_partners_b = M.get_partners(b);
  for(auto & partner : matched_partners_b ){
    auto a_prime = partner.vertex ;
    if(b->get_preference_list().prefers(a,a_prime)==cBetter){
      check_b_blocking = true ;
      break ;
    }
  }
  return check_a_blocking && check_b_blocking ;
}

bool check_justify(VertexPtr a , VertexPtr b , Matching &M)
{
  //checking if a is fully subscribed and all of its neighbours which 
  // are lesser preferred than b are not surplus
  bool a_justify = M.number_of_partners(a)==(a->get_upper_quota()) ;
  for(auto & partner : M.get_partners(a)){
    auto b_prime = partner.vertex ;
    if(a->get_preference_list().prefers(b,b_prime)==cBetter){

      if((M.number_of_partners(b_prime))>(b_prime->get_lower_quota())){
        a_justify= false ;
        break ;
      }
      }
    }
  

  //checking if b is fully subscribed and all of its neighbours which 
  // are lesser preferred than a are not surplus
  bool b_justify = M.number_of_partners(b)==(b->get_upper_quota()) ;
  for(auto & partner : M.get_partners(b)){
    auto a_prime = partner.vertex ;
    if(b->get_preference_list().prefers(a,a_prime)==cBetter){
      if((M.number_of_partners(a_prime))>(a_prime->get_lower_quota())){
        b_justify= false ;
        break ;
      }
    }
  }
  return a_justify || b_justify ; //return true if at least one of a or b can justify
}

bool ManyToManyCriticalRSM::verify( Matching &M) const
{
  
  std::shared_ptr<BipartiteGraph> G = get_graph();

  const auto& A_partition =G->get_A_partition();
  const auto& B_partition =G->get_B_partition();
                                                       
                                                        
  bool check_RSM = true ;
  for (const auto& [_, a] : A_partition) 
  {
    //checking if any a in proposing partition is part of an unjustified blocking pair
    auto a_prefS = (a->get_preference_list()).get_prefS();
    for(auto &partner : a_prefS)
    {
      auto b = partner.vertex ;
      if(!M.is_matched_to(a,b))
      {
        if(check_blocking_pair(a,b,M))
        {
          if(!check_justify(a,b,M))
          {
            //printing the Unjustified Blocking pair
            std::cout<<"Unjustified Blocking pair :"<<a->get_id()<<" "<<b->get_id()<<std::endl;
            check_RSM = false ;
          }
        }
      }
    }
  } 
  return check_RSM ;
}

void ManyToManyCriticalRSM::critical_propose(FreeListType& free_list, const VertexPtr a, const VertexPtr b,int q_a,int q_b, std::map<VertexPtr, VertexBookkeeping>& bookkeep_data, Matching& M,std::unordered_map<VertexPtr, std::vector<VertexPtr>> &t_star_partners)
{
  auto &a_data = bookkeep_data[a];
  auto l = a_data.level;
  auto &b_pref_list = b->get_preference_list();
  // updating the level if a is already a matched to b at a lower level
  if(M.is_matched_to(a,b))
  {
    const auto &partners = M.get_partners(b);
    const auto &partner_it = partners.find(a);
    if(partner_it->level<l)
    {
      M.remove_partner(a,b);
      add_matched_partners(M, a, b, a_data, b_pref_list);
    
      // remove from t_star_partners if a is already matched at t* and l>t  
      auto a_itr = t_star_partners[b].begin();
      while(a_itr!=t_star_partners[b].end())
      {
        if(*a_itr==a)
        {
          t_star_partners[b].erase(a_itr);
          break;
        }
        a_itr++;
      }
    }
  }
  else if (M.number_of_partners(b)<q_b) // if |M(b)| <q_b then add (a^l,b) to matching
  {
    add_matched_partners(M, a, b, a_data, b_pref_list);
  } 
  else if(M.number_of_partners(b)==q_b)// if |M(b)| == q_b  
  { 

    auto least_preferred_partner = M.get_partners(b).get_least_preferred();
    auto y =  least_preferred_partner.level;
    auto aj = least_preferred_partner.vertex;
    if((l > y) || ((l == y) && (b_pref_list.prefers(a, aj))==cBetter)) 
    {
      M.remove_partner(aj, b);
      add_matched_partners(M, a, b, a_data, b_pref_list);

      // add a_j^y to Q if there is no other a_j^x in Q already
      auto &aj_data = bookkeep_data[aj];
      if (not aj_data.in_free_list) {
        aj_data.in_free_list = true;
        bookkeep_data[aj].level = y;
        add_to_free_list(free_list, aj);
      }

      // remove aj from t_star_partners if it was matched to b at t* level
      auto a_itr = t_star_partners[b].begin();
      while(a_itr!=t_star_partners[b].end()){
        if(*a_itr==aj){
          t_star_partners[b].erase(a_itr);
          break;
        }
        a_itr++;
      }
    } 
  }

  if(M.number_of_partners(a)<q_a) // if |M(a)| < q_a  then add a^l to Q 
  {
    add_to_free_list(free_list, bookkeep_data[a],a);
  }
  
}


void ManyToManyCriticalRSM::ties_propose(FreeListType& free_list, VertexPtr a, const PreferenceList& a_pref_list, std::map<VertexPtr, VertexBookkeeping>& bookkeep_data, Matching& M, std::unordered_map<VertexPtr, std::vector<VertexPtr>> &t_star_partners,const int t, std::unordered_map<VertexPtr,std::vector<VertexPtr>>& proposed_vertices) {
  auto &a_data = bookkeep_data[a];
  auto b = favourite_neighbour(a, a_pref_list, a_data, M,proposed_vertices);
  proposed_vertices[a].push_back(b);
  
  auto k = compute_rank(b, a_pref_list) - 1; // 0 index
  auto l = a_data.level;
  auto &b_pref_list = b->get_preference_list();

  //setting all the uncertain proposals at rank k-1 in pref of a as certain proposals
  for(auto &b_prime : M.get_partners(a))
  {
      if(M.uncertain_proposals.find(b_prime.vertex)!=M.uncertain_proposals.end())
      {
        auto &b_prime_uncertain_proposals = M.uncertain_proposals[b_prime.vertex];
        auto uncertain_partner_it = b_prime_uncertain_proposals.begin();
        while(uncertain_partner_it!=b_prime_uncertain_proposals.end())
        {
          //if a^l,b_prime is uncertain, b_prime is (k-1)th ranked neighbour 
          if(uncertain_partner_it->vertex==a && uncertain_partner_it->level==l &&  b_prime.rank==k)
          {
            b_prime_uncertain_proposals.erase(uncertain_partner_it);   
            if(M.uncertain_proposals[b_prime.vertex].size()==0) M.uncertain_proposals.erase(b_prime.vertex);
            break;
          }
          uncertain_partner_it++;
        }
      }
  }

  //unmark b if it is already marked by it
  if (a_data.marked.find(b)!=a_data.marked.end()) {
    a_data.marked.erase(b);
  }


  if(M.is_matched_to(a,b)) 
  // update the level of a if a is already matched to b
  {
    const auto &partners = M.get_partners(b);
    const auto &partner_it = partners.find(a);
    if(partner_it->level<l)
    {
      M.remove_partner(a,b);
      add_matched_partners(M, a, b, a_data, b_pref_list);
      if(l==t && a_data.star){
        t_star_partners[b].push_back(a);
      }
    }
    else if(l==t && a_data.star && partner_it->level==t)
    {
      M.remove_partner(a,b);
      add_matched_partners(M, a, b, a_data, b_pref_list);     
      t_star_partners[b].push_back(a);
    }
  }
  else 
  {
    // update capacity of b if b has a neighbour matched to it at a level less than t
    if(M.is_matched_lt(b,t))
    {
      bookkeep_data[b].residual = b->get_lower_quota();
    }
    else
    {
      bookkeep_data[b].residual = b->get_upper_quota();
    }



    if(M.number_of_partners(b)<bookkeep_data[b].residual) // if |M(b)| <c(b)
    {
      add_matched_partners(M, a, b, a_data, b_pref_list);
      if(bookkeep_data[a].star)
      {
        t_star_partners[b].push_back(a);
      }
      else
      {
          //set uncertain proposal line 12 & 13
          if(a_pref_list.is_tied(k))
          {
            bool is_uncertain = false;
            auto &partners = a_pref_list.get_ties(k);
            for(auto &partner: partners)
            {
              auto b_prime = partner.vertex;
              
              if((M.number_of_partners(b_prime)<(b_prime->get_upper_quota())) && (proposed_vertices.find(a)==proposed_vertices.end() || (std::find((proposed_vertices[a]).begin(),(proposed_vertices[a]).end(),b_prime)==proposed_vertices[a].end()) ))
              {
                is_uncertain = true;
                break;
              }
            }
            if(is_uncertain)
            {       
              M.set_uncertain_proposal(a,b,k,l); // clarify the parameters
              
            }
          }
      }
    }



    else //|M(b)| == c(b)
    {
        if(M.is_matched_lt(b,t))
        {
          auto &b_partners =  M.get_partners(b);
          auto aj_partner = b_partners.get_least_preferred();
          auto &aj = aj_partner.vertex;
          auto y = aj_partner.level;
          M.remove_partner(aj, b);
          add_matched_partners(M, a, b, a_data, b_pref_list);

          // add a_j^y to Q if there is no other a_j^x in Q already
          auto &aj_data = bookkeep_data[aj];
          if (not aj_data.in_free_list) {
            aj_data.in_free_list = true;
            bookkeep_data[aj].level = y;
            add_to_free_list(free_list, aj);
          }
          if(a_data.star)
          {
            t_star_partners[b].push_back(a);
          }
        }
        else if(M.check_uncertain_proposal(b))
        {
          auto &aj_partner = M.uncertain_proposals[b][M.uncertain_proposals[b].size()-1];
          auto aj=aj_partner.vertex;
          auto y = aj_partner.level;
      
          M.uncertain_proposals[b].pop_back();

          if(M.uncertain_proposals[b].size()==0) M.uncertain_proposals.erase(b);
         
          M.remove_partner(aj, b);
        
          add_matched_partners(M, a, b, a_data, b_pref_list);
        

          // add a_j^y to Q if there is no other a_j^x in Q already
          auto &aj_data = bookkeep_data[aj];
          if (not aj_data.in_free_list) {
            aj_data.in_free_list = true;
            bookkeep_data[aj].level = y;
            add_to_free_list(free_list, aj);
          }
          if(a_data.star)
          {
            t_star_partners[b].push_back(a);
          }
          
          aj_data.marked[b] = true;
         
        }
        else if( M.get_partners(b).get_least_preferred().level==t)
        {
          
            auto &b_partners = M.get_partners(b);
            auto least_preferred = ( M.get_partners(b).get_least_preferred()).vertex;
            auto star_status = false;
            if(t_star_partners.find(b)!=t_star_partners.end())
            {
              if(std::find(t_star_partners[b].begin(),t_star_partners[b].end(),least_preferred)!=t_star_partners[b].end())
              {
                  star_status = true; 
              }
            }

            for(auto a_prime_partner:b_partners)
            {
              if(a_prime_partner.level==t)
              {
                if(b_pref_list.prefers(least_preferred,a_prime_partner.vertex)==cBetter)
                {
                    least_preferred = a_prime_partner.vertex;
                    if(t_star_partners.find(b)!=t_star_partners.end())
                   {
                      if(std::find(t_star_partners[b].begin(),t_star_partners[b].end(),least_preferred)!=t_star_partners[b].end())
                    {
                        star_status = true; 
                      }
                    }

                }
                else if(b_pref_list.prefers(least_preferred,a_prime_partner.vertex)==cEqual)
                {
                   if(star_status)
                   {
                      bool a_prime_star_status = false;
                      if(t_star_partners.find(b)!=t_star_partners.end())
                      {
                      if(std::find(t_star_partners[b].begin(),t_star_partners[b].end(),a_prime_partner.vertex)!=t_star_partners[b].end())
                      {
                        a_prime_star_status = true; 
                      }
                     }
                     if(!a_prime_star_status)
                     {
                        star_status = a_prime_star_status;
                        least_preferred = a_prime_partner.vertex;
                     }
                   }
                }
              }
            }
            if(b_pref_list.prefers(a,least_preferred)==cBetter)
            {
              M.remove_partner(least_preferred, b);
              add_matched_partners(M, a, b, a_data, b_pref_list);

              auto aj = least_preferred;
          // add a_j^y to Q if there is no other a_j^x in Q already
              auto &aj_data = bookkeep_data[least_preferred];
              if (not aj_data.in_free_list) {
                  aj_data.in_free_list = true;
                  bookkeep_data[aj].level = t;
                  bookkeep_data[aj].star = star_status;
                add_to_free_list(free_list, aj);
                }
              
              if(a_data.star)
              {
                t_star_partners[b].push_back(a);
              }

              if(star_status)
              {
                 auto a_itr = t_star_partners[b].begin();
                while(a_itr!=t_star_partners[b].end()){
                  if(*a_itr==aj){
                  t_star_partners[b].erase(a_itr);
                break;
                  }
                a_itr++;
                  }
              }
            }
            else if(b_pref_list.prefers(a,least_preferred)==cEqual)
            {
              if(!star_status && a_data.star)
              {
                 M.remove_partner(least_preferred, b);
              add_matched_partners(M, a, b, a_data, b_pref_list);

              auto aj = least_preferred;
          // add a_j^y to Q if there is no other a_j^x in Q already
              auto &aj_data = bookkeep_data[least_preferred];
              if (not aj_data.in_free_list) {
                  aj_data.in_free_list = true;
                  bookkeep_data[aj].level = t;
                  bookkeep_data[aj].star = star_status;
                add_to_free_list(free_list, aj);
                }
                t_star_partners[b].push_back(a);
          
              }
            }
        }
    }
  }
  // Rest of the Ties Propose
  if(M.number_of_partners(a)<a->get_upper_quota()) add_to_free_list(free_list, bookkeep_data[a],a);
}


VertexPtr ManyToManyCriticalRSM::favourite_neighbour(VertexPtr a, const PreferenceList& a_pref_list, VertexBookkeeping &a_data, const Matching& M, std::unordered_map<VertexPtr,std::vector<VertexPtr>> proposed_vertices) {
  // k is the best rank at which some
  // unproposed or marked neighbours of u exist
  // u_data.begin gives the highest rank at which an unproposed vertex exists
  auto k = a_data.begin;

  if(!a_pref_list.is_tied(k))
  {
    a_data.begin++;
    a_data.tied_index = 0;
    return a_pref_list.at(k).vertex;
  }
  else
  {
    auto &partners = a_pref_list.get_ties(k);
    
    // case 1
    for(auto &partner: partners)
    {
      auto b_prime = partner.vertex;
     
      if((M.number_of_partners(b_prime)<(b_prime->get_upper_quota()) )&& (proposed_vertices.find(a)==proposed_vertices.end() || (std::find((proposed_vertices[a]).begin(),(proposed_vertices[a]).end(),b_prime)==proposed_vertices[a].end()) ))
      {
        // proposed_vertices[a].push_back()
        a_data.tied_index++;
        if(a_data.tied_index==partners.size() && a_data.marked.size()==0) 
        {
          a_data.tied_index = 0;
          a_data.begin++;
        }
        return b_prime;
      }
    }

    //case 2

    for(auto &partner: partners)
    {
      auto b_prime = partner.vertex;
      if(proposed_vertices.find(a)==proposed_vertices.end() || (std::find((proposed_vertices[a]).begin(),(proposed_vertices[a]).end(),b_prime)==proposed_vertices[a].end()) )
      {
        // proposed_vertices[a].push_back()
        a_data.tied_index++;
        if(a_data.tied_index==partners.size() && a_data.marked.size()==0) 
        {
          a_data.tied_index = 0;
          a_data.begin++;
        }
        return b_prime;
      }

    }

    // case 3

    for(auto &partner:partners)
    {
      auto b_prime = partner.vertex;
      if(a_data.marked.find(b_prime)!=a_data.marked.end())
      {
        if(a_data.tied_index==partners.size() && a_data.marked.size()==1) 
        {
          a_data.tied_index = 0;
          a_data.begin++;
        }
        return b_prime; 
      }
    }
    return nullptr;
  }
}


