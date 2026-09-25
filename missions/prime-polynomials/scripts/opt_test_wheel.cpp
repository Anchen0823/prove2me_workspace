#define main campaign_main
#include "opt_wheel17_search.cpp"
#undef main
#include <cassert>
bool admits(vector<ll> co,int radius,int target){
 int c=co.back();co.back()=0;bool ok[15][48];
 for(int j=0;j<15;j++){int p=ps[j];fill(ok[j],ok[j]+p,true);for(int x=0;x<p;x++)ok[j][(-eval(co,x)%p+p)%p]=false;}
 vector<ll> values;for(int x=-radius;x<=radius;x++)values.push_back(eval(co,x));sort(values.begin(),values.end());
 bool rescued;return exception_possible(ok,values,c,target,rescued);
}
int main(){
 isp.assign(N+1,true);isp[0]=isp[1]=false;for(int p=2;p*p<=N;p++)if(isp[p])for(int j=p*p;j<=N;j+=p)isp[j]=false;
 for(int p=2;p<=100000;p++)if(isp[p])primes.push_back(p);
 unsigned cases=0,positive=0;
 for(int a=-12;a<=12;a++)if(a)for(int b=-12;b<=12;b++)for(int c=-12;c<=12;c++){
  vector<ll> co={a,b,c};int len=scan(co,12).len;
  for(int target=1;target<=10;target++){cases++;if(len>=target){positive++;assert(admits(co,12,target));}}
 }
 assert(scan({4,0,7},6).len==7);assert(admits({4,0,7},6,7));
 vector<ll> quintic={3,7,-340,-122,3876,997};assert(scan(quintic,80).len==49);assert(admits(quintic,80,47));
 mt19937 gen(1937); unsigned long long wheel_cases=0;
 for(int shape=0;shape<100;shape++){
  vector<ll> co={1+gen()%256,gen()%300,ll(gen()%120001)-60000,0};bool ok[15][48];
  for(int j=0;j<7;j++){int p=ps[j];fill(ok[j],ok[j]+p,true);for(int x=0;x<p;x++)ok[j][(-eval(co,x)%p+p)%p]=false;}
  vector<int> residues={0};int modulus=1;
  for(int j=0;j<7;j++){vector<int> next;int p=ps[j];for(int k=0;k<p;k++)for(int r:residues){int v=r+k*modulus;if(ok[j][v%p])next.push_back(v);}residues.swap(next);modulus*=p;}
  assert(modulus==W);assert(is_sorted(residues.begin(),residues.end()));
  size_t cursor=0;
  for(int r=0;r<W;r++){bool pass=true;for(int j=0;j<7;j++)if(!ok[j][r%ps[j]]){pass=false;break;}bool actual=cursor<residues.size() && residues[cursor]==r;if(actual)cursor++;assert(actual==pass);wheel_cases++;}
 }
 cerr<<"wheel_equivalence_cases="<<wheel_cases<<" mismatches=0"<<endl;
 cout<<"{\"cases\":"<<cases<<",\"positive_cases\":"<<positive<<",\"false_negatives\":0,\"small_prime_exception\":true,\"49_term_fixture\":true}"<<endl;
}

