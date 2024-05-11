#include <iostream>
#include <vector>
#include <random>
#include <algorithm>
#include <string>
#include <chrono>

using namespace std ;

int main(int argc, char* argv[]){

    int M =stoi(argv[1]);

    int N = stoi(argv[2]);

    vector<string> A_partition ;
    vector<string> B_partition ;

    for(int i=0;i<M;i++){
        A_partition.push_back("a"+to_string(i));
    }

    for(int i=0;i<N;i++){
        B_partition.push_back("b"+to_string(i));
    }

    vector<string> ppref_lists_A [M];
    vector<string> ppref_lists_B [N] ;

    for(int i =0;i<M;i++){
        for(int j=0;j<N;j++){

            if(ppref_lists_A[i].size()==0 || ppref_lists_B[j].size()==0){
                string a = A_partition[i];
                string b = B_partition[j];

                ppref_lists_A[i].push_back(b);
                ppref_lists_B[j].push_back(a);

                continue;
            }
            int randomValue = std::rand() % 3;

            if(randomValue==1){
                string a = A_partition[i];
                string b = B_partition[j];

                ppref_lists_A[i].push_back(b);
                ppref_lists_B[j].push_back(a);
            }
        }
    }

    cout<<"@PartitionA"<<endl;
    for(int i = 0;i<M;i++){

        // int lower_quota = rand()%(ppref_lists_A[i].size()/5+2);
        // int upper_quota = std::max(1,lower_quota+rand()%((int)ppref_lists_A[i].size()-lower_quota));
        // cout<<A_partition[i]<<" ("<<lower_quota<<","<<upper_quota<<")";
        cout<<A_partition[i]<<" ("<<rand()%2<<","<<"1)";
        if(i!=M-1) cout<<" , ";
    }

    cout<<";"<<endl;
    cout<<"@End"<<endl;
    cout<<endl;

    cout<<"@PartitionB"<<endl;
    
    for(int i = 0;i<N;i++){
        int lower_quota = rand()%(ppref_lists_B[i].size()/5+2);
        int upper_quota = std::max(1,lower_quota+rand()%((int)ppref_lists_B[i].size()-lower_quota));
        cout<<B_partition[i]<<" ("<<lower_quota<<","<<upper_quota<<")";
        if(i!=N-1) cout<<" , ";
    }

    cout<<";"<<endl;
    cout<<"@End"<<endl;
    cout<<endl;

    cout<<"@PreferenceListsA"<<endl;

    for(int i=0;i<M;i++){
        unsigned seed = chrono::system_clock::now().time_since_epoch().count();
        std::shuffle(ppref_lists_A[i].begin(), ppref_lists_A[i].end(), std::default_random_engine(seed));

        bool is_open = false ;
        int last_opened = -1 ;
        cout<<A_partition[i]<<" : ";
        for(int k =0;k<ppref_lists_A[i].size();k++){
            int randomValue = std::rand() % 2;

            if(is_open==false && randomValue==0 &&  k!=ppref_lists_A[i].size()-1){
                last_opened=k;
                cout<< "( ";
                is_open=true ;
            }

                cout<<ppref_lists_A[i][k]<<" ";


            if(is_open==true && randomValue==1 && k-last_opened>=2 && k!=ppref_lists_A[i].size()-1){
                cout<< ") ";
                is_open=false ;
            }

            if(k!=ppref_lists_A[i].size()-1){
                    cout<<", ";
                }

            if(is_open==true && randomValue==1 && k==ppref_lists_A[i].size()-1){
                cout<< ") ";
                is_open=false ;
            }
        }

        if(is_open){
             cout<< ") ";
             is_open==false ;
        }

        cout<<";"<<endl;


    }
    cout<<"@End"<<endl;
    cout<<endl;
    cout<<"@PreferenceListsB"<<endl;
    for(int i=0;i<N;i++){
        unsigned seed = chrono::system_clock::now().time_since_epoch().count();
        std::shuffle(ppref_lists_B[i].begin(), ppref_lists_B[i].end(), std::default_random_engine(seed));

        bool is_open = false ;
        int last_opened = -1 ;

        cout<<B_partition[i]<<" : ";
        for(int k =0;k<ppref_lists_B[i].size();k++){
            int randomValue = std::rand() % 2;

            if(is_open==false && randomValue==0 && k!=ppref_lists_B[i].size()-1){
                last_opened=k;
                cout<< "( ";
                is_open=true ;
            }

                cout<<ppref_lists_B[i][k]<<" ";
                

            if(is_open==true && randomValue==1 && k-last_opened>=2&&k!=ppref_lists_B[i].size()-1){
                cout<< ") ";
                is_open=false ;
            }

            if(k!=ppref_lists_B[i].size()-1){
                    cout<<", ";
                }

            if(is_open==true && randomValue==1 && k==ppref_lists_B[i].size()-1){
                cout<< ") ";
                is_open=false ;
            }
        }

        if(is_open){
             cout<< ") ";
             is_open==false ;
        }

        cout<<";"<<endl;


    }

    cout<<"@End"<<endl;
    



}

