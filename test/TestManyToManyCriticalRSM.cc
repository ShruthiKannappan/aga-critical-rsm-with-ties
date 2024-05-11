#include <GraphReader.h>
#include <Utils.h>
#include "TestDefs.h"
#include <ManyToManyCriticalRSM.h>
#include <iostream>

TEST_CASE("ManyToManyCriticalRSM critical_rsm_many", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/critical_rsm.txt"));
    auto a1 = get_vertex_by_id(G, "a1");
    auto a2 = get_vertex_by_id(G, "a2");
    auto a3 = get_vertex_by_id(G, "a3");
    auto b1 = get_vertex_by_id(G, "b1");
    auto b2 = get_vertex_by_id(G, "b2");
    auto b3 = get_vertex_by_id(G, "b3");
    auto b4 = get_vertex_by_id(G, "b4");

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST 0 COMPLETED!"<<std::endl;
}


SECTION("NO BLOCKING PAIR VERIFY TEST"){
    Matching M = new Matching(true);
    M.add_partner(a1,b1,1,1);
    M.add_partner(a2,b4,1,1);
    M.add_partner(a3,b3,1,1);

    M.add_partner(b1,a1,1,1);
    M.add_partner(b4,a2,1,1);
    M.add_partner(b3,a3,1,1);

    auto verifier = new ManyToManyCriticalRSM(G,true);

    assert( (verifier->verify(M)) == true);
    std::cout<<"VERIFY TEST 1 COMPLETED!"<<std::endl;
}

SECTION("JUSTIFIED BLOCKING PAIRS VERIFY TEST")
{
     Matching M = new Matching(true);
    M.add_partner(a1,b2,1,1);
    M.add_partner(a2,b4,1,1);
    M.add_partner(a3,b3,1,1);
        
    M.add_partner(b2,a1,1,1);
    M.add_partner(b4,a2,1,1);
    M.add_partner(b3,a3,1,1);


    auto verifier = new ManyToManyCriticalRSM(G,true);

    assert( (verifier->verify(M) )== true);
    std::cout<<" VERIFY TEST 2 COMPLETED!"<<std::endl;
}
    
    SECTION("NON-JUSTIFIED BLOCKING PAIRS")
    {
    Matching M = new Matching(true);
    M.add_partner(b1,a2,1,1);
    M.add_partner(b3,a3,1,1);

    M.add_partner(a2,b1,1,1);
    M.add_partner(a3,b3,1,1);
    auto verifier = new ManyToManyCriticalRSM(G,true);
    assert( (verifier->verify(M)) == false);
    std::cout<<"VERIFY TEST 3 COMPLETED!"<<std::endl;
    }

}

TEST_CASE("ManyToManyCriticalRSM critical_rsm_many1", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm.txt"));
    auto a1 = get_vertex_by_id(G, "a1");
    auto a2 = get_vertex_by_id(G, "a2");
    auto b1 = get_vertex_by_id(G, "b1");
    auto b2 = get_vertex_by_id(G, "b2");
    auto b3 = get_vertex_by_id(G, "b3");

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST 1 COMPLETED!"<<std::endl;
}


SECTION("NON-JUSTIFIED BLOCKING PAIRS"){
    Matching M = new Matching(true);
    M.add_partner(a1,b2,1,1);
    M.add_partner(a2,b1,1,1);
    M.add_partner(a2,b3,1,1);
    M.add_partner(a2,b2,1,1);
    M.add_partner(a1,b3,1,1);

    M.add_partner(b2,a1,1,1);
    M.add_partner(b1,a2,1,1);
    M.add_partner(b3,a2,1,1);
    M.add_partner(b2,a2,1,1);
    M.add_partner(b3,a1,1,1);

    auto verifier = new ManyToManyCriticalRSM(G,true);
    assert((verifier->verify(M)) == false);
    std::cout<<"VERIFY TEST 4 COMPLETED!"<<std::endl;
}   
}

TEST_CASE("ManyToManyCriticalRSM critical_rsm_many2", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm2.txt"));
    auto a1 = get_vertex_by_id(G, "a1");
    auto a2 = get_vertex_by_id(G, "a2");
    auto b1 = get_vertex_by_id(G, "b1");
    auto b2 = get_vertex_by_id(G, "b2");
    auto b3 = get_vertex_by_id(G, "b3");

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST 2 COMPLETED!"<<std::endl;
}


SECTION("JUSTIFIED BLOCKING PAIRS VERIFY TEST"){
    Matching M = new Matching(true);
    M.add_partner(a1,b2,1,1);
    M.add_partner(a2,b1,1,1);
    M.add_partner(a2,b3,1,1);
    M.add_partner(a1,b3,1,1);

    M.add_partner(b2,a1,1,1);
    M.add_partner(b1,a2,1,1);
    M.add_partner(b3,a2,1,1);
    M.add_partner(b3,a1,1,1);
    auto verifier = new ManyToManyCriticalRSM(G,true);

    assert( (verifier->verify(M)) == true);
    std::cout<<"VERIFY TEST 5 COMPLETED!"<<std::endl;
}


    
}

TEST_CASE("ManyToManyCriticalRSM critical_rsm_many5", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm5.txt"));

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST SIZE 10 COMPLETED!"<<std::endl;
}
}
TEST_CASE("ManyToManyCriticalRSM critical_rsm_many6", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm6.txt"));

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST SIZE 20 COMPLETED!"<<std::endl;
}
}
TEST_CASE("ManyToManyCriticalRSM critical_rsm_many7", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm7.txt"));

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST SIZE 30 COMPLETED!"<<std::endl;
}
}
TEST_CASE("ManyToManyCriticalRSM critical_rsm_many8", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm8.txt"));

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST SIZE 40 COMPLETED!"<<std::endl;
}
}
TEST_CASE("ManyToManyCriticalRSM critical_rsm_many9", "[matching_manytomanycriticalrsm]") {

    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm9.txt"));

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST SIZE 50 COMPLETED!"<<std::endl;
}
}
TEST_CASE("ManyToManyCriticalRSM critical_rsm_many10", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm10.txt"));

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST SIZE 100 COMPLETED!"<<std::endl;
}
}
TEST_CASE("ManyToManyCriticalRSM critical_rsm_many11", "[matching_manytomanycriticalrsm]") {
    auto G = read_graph(get_filepath(get_resources_dir(), "/many_critical_rsm11.txt"));

SECTION("COMPUTE MATCHING TEST")
{
    ManyToManyCriticalRSM manycrsm(G,true);
    Matching M = manycrsm.compute_matching();
    assert( (manycrsm.verify(M)) == true);
    std::cout<<"COMPUTE MATCHING TEST SIZE 100,40 COMPLETED!"<<std::endl;
}
}