// Rational quintic family: numerator / 4. Odd primes have period p; at 2 use period 8.
// Perturb numerator coefficients by 840 = 4*210, preserving integer values.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
using ll=long long;
const int N=50000000, W=9240;
vector<bool> isp;
vector<int> primes;
int ps[]={2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53};
bool exception_possible(const bool ok[][54],const vector<ll>& values,int c,int target,bool& rescued){
 rescued=false;
 for(int j=0;j<16 && ps[j]<=target;j++){
  int p=ps[j];if(ok[j][(c%p+p)%p])continue;
  if(2*p<=target)return false;
  if(!binary_search(values.begin(),values.end(),ll(p)-c) &&
     !binary_search(values.begin(),values.end(),-ll(p)-c))return false;
  rescued=true;
 }return true;
}
ll eval(const vector<ll>& c,int x){ll v=0;for(ll a:c)v=v*x+a; if(v%4)throw runtime_error("nonintegral output");return v/4;}
bool prime(ll v){if(v<2)return false;if(v<=N)return isp[v];for(int p:primes){if(1LL*p*p>v)return true;if(v%p==0)return false;}throw runtime_error("prime trial table insufficient");}
struct Result {int len=0,lo=0,hi=0;vector<ll> co;};
Result scan(const vector<ll>& co,int radius){
 Result best;unordered_map<ll,int> last;int start=-radius;
 for(int x=-radius;x<=radius;x++){
  ll v=llabs(eval(co,x));if(!prime(v)){last.clear();start=x+1;continue;}
  auto it=last.find(v);if(it!=last.end())start=max(start,it->second+1);last[v]=x;
  if(x-start+1>best.len)best={x-start+1,start,x,co};
 }return best;
}
void emit(ostream& o,const Result&r){o<<"{\"length\":"<<r.len<<",\"lo\":"<<r.lo<<",\"hi\":"<<r.hi<<",\"denominator\":4,\"coefficients\":[";for(size_t i=0;i<r.co.size();i++){if(i)o<<",";o<<r.co[i];}o<<"]}";}
int main(int argc,char**argv){
 int degree=argc>1?stoi(argv[1]):8; if(degree!=8)throw runtime_error("only rational quintic mode 8 supported");double seconds=argc>2?stod(argv[2]):60;
 unsigned seed=argc>3?stoul(argv[3]):20260924;string prefix=argc>4?argv[4]:"campaign";
 size_t shape_limit=argc>5?stoull(argv[5]):0;
 int mutation_radius=argc>7?stoi(argv[7]):10;
 if(mutation_radius<1 || mutation_radius>50)throw runtime_error("mutation radius must be 1..50");
 string strategy=argc>6?argv[6]:"exception";
 if(strategy!="exception" && strategy!="baseline")throw runtime_error("unknown strategy");
 auto t0=chrono::steady_clock::now();isp.assign(N+1,true);isp[0]=isp[1]=false;
 for(int p=2;p*p<=N;p++)if(isp[p])for(int j=p*p;j<=N;j+=p)isp[j]=false;
 for(int p=2;p<=2000000;p++)if(isp[p])primes.push_back(p);
 auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-t0).count();};
 if(degree==0){for(auto co:vector<vector<ll>>{{36,18,-1801},{66,83,-13735,30139},{1,1,41},{1,-106,3959,-60950,341227}}){emit(cout,scan(co,80));cout<<endl;}return 0;}
 if(degree==-1){auto t=chrono::steady_clock::now();ll sum=0;for(int c=-5000;c<5000;c++)sum+=scan({36,18,c},80).len;cout<<"{\"checksum\":"<<sum<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-t).count()<<"}"<<endl;return 0;}
 mt19937 rng(seed);ofstream log(prefix+".jsonl");Result best;unsigned long long shapes=0,completed_shapes=0,presieved=0,tested=0,passed23=0,rescued=0;
 unordered_set<string> visited;
 // For a DISTINCT run of length >=47, a root modulo p<=23 is impossible:
 // two inputs in that residue force the same absolute prime p. Thus this
 // filter is lossless for the target, including exceptional +/-p values.
 // Coefficient sampling remains non-exhaustive; inputs are bounded.
 const size_t finite_shapes=degree==8?size_t(1+16*mutation_radius+24*mutation_radius*mutation_radius):(degree==2?131840:(degree==4?578289:0));
 while(elapsed()<seconds && (!finite_shapes || visited.size()<finite_shapes) && (!shape_limit || shapes<shape_limit)){
  vector<ll> co;
  if(degree==8){co={1,2,-345,1758,70000,0};if(shapes){for(int k=0;k<2;k++){int j=1+rng()%4;co[j]+=840*((int)(rng()%(2*mutation_radius+1))-mutation_radius);}}}
  else if(degree==7){int a=8+rng()%17,b=20+rng()%17,c=-2185+rng()%1001,d=-24807+rng()%2001;co={a,b,c,d,0};}
  else if(degree==2){int a=1+rng()%512,b=rng()%(a+1);co={a,b,0};}
  else if(degree==4){int a=58+rng()%17,b=75+rng()%17,c=-13735+(int)(rng()%2001)-1000;co={a,b,c,0};}
  else if(degree==6){int a=1+rng()%16,b=rng()%(2*a+1),c=(int)(rng()%2001)-1000,d=(int)(rng()%40001)-20000;co={a,b,c,d,0};}
  else {int a=1+rng()%256,b=rng()%(3*a/2+1),c=(int)(rng()%120001)-60000;co={a,b,c,0};}
  string key;for(size_t j=0;j+1<co.size();j++)key+=to_string(co[j])+",";
  if(!visited.insert(key).second)continue;
  shapes++;bool ok[16][54];bool possible=true;
  for(int j=0;j<16;j++){int p=ps[j];fill(ok[j],ok[j]+p,true);for(int x=0;x<(p==2?8:p);x++){int r=(int)((-eval(co,x)%p+p)%p);ok[j][r]=false;}if(j<9 && count(ok[j],ok[j]+p,true)==0){possible=false;break;}}
  if(!possible){completed_shapes++;continue;}
  vector<ll> shape_values;for(int x=-80;x<=80;x++)shape_values.push_back(eval(co,x));sort(shape_values.begin(),shape_values.end());
  vector<int> residues;for(int r=0;r<W;r++){bool pass=true;for(int j=0;j<5;j++)if(!ok[j][r%ps[j]]){pass=false;break;}if(pass)residues.push_back(r);}
  bool shape_complete=true;
  for(int base=-54*W;base<=54*W;base+=W){
   if(elapsed()>=seconds){shape_complete=false;break;}
   for(int r:residues){
   int constant=base+r;presieved++;bool pass=true;for(int j=5;j<9;j++)if(!ok[j][(constant%ps[j]+ps[j])%ps[j]]){pass=false;break;}if(!pass)continue;
   passed23++;bool exception=false;
   if(strategy=="exception")pass=exception_possible(ok,shape_values,constant,(degree==8?58:47),exception);
   if(!pass)continue;if(exception)rescued++;
   co.back()=4LL*constant;tested++;auto found=scan(co,80);
   if(found.len>best.len){best=found;emit(cout,best);cout<<endl;emit(log,best);log<<endl;}
   }
  }
  if(shape_complete)completed_shapes++;
 }
 string termination_reason=completed_shapes==finite_shapes?"finite_family_exhausted":(elapsed()>=seconds?"time_budget":"shape_limit");
 ofstream out(prefix+".json");out<<"{\"budget_seconds\":"<<seconds<<",\"completed_shapes\":"<<completed_shapes<<",\"termination_reason\":\""<<termination_reason<<"\",\"mutation_radius\":"<<mutation_radius<<",\"target_length\":"<<(degree==8?58:47)<<",\"strategy\":\""<<strategy<<"\",\"passed23\":"<<passed23<<",\"rescued_candidates\":"<<rescued<<",\"shape_limit\":"<<shape_limit<<",";out<<"\"degree\":"<<(degree==8?5:(degree>=6?4:(degree==2?2:3)))<<",\"mode\":"<<degree<<",\"deduplicated_shapes\":true,\"seed\":"<<seed<<",\"seconds\":"<<elapsed()<<",\"shapes\":"<<shapes<<",\"wheel_candidates\":"<<presieved<<",\"scanned_polynomials\":"<<tested<<",\"root_free_primes_through\":23,\"radius\":80,\"best\":";emit(out,best);out<<"}\n";
 cout<<"DONE shapes="<<shapes<<" wheel_candidates="<<presieved<<" scanned="<<tested<<" seconds="<<elapsed()<<endl;
}
