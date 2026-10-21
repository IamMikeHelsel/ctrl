// heuristic5.c -- Monte-Carlo estimate of the expected number of coprime solutions A+B+C=D (all 5-full)
// per decade of D.  Model: P(D is 5-full | D) ~ dens(D) * prod_{p<=11} rho_p(D mod p^5), where dens is the
// empirical density of 5-full numbers near D and rho_p(r) = p^5 * (fraction of 5-full numbers that are = r mod p^5)
// (empirical, from the list itself).  Triples are sampled uniformly from the list of 5-full numbers <= N.
// build: cc -O3 -o heuristic5 heuristic5.c    usage: ./heuristic5 N samples
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128; typedef uint64_t u64; typedef uint32_t u32;
static u128 parse128(const char *s){ u128 v=0; for(;*s;s++){ if(*s<'0'||*s>'9') break; v=v*10+(u128)(*s-'0'); } return v; }
static u128 gcd128(u128 a,u128 b){ while(b){ u128 t=a%b; a=b; b=t; } return a; }
static u128 N; static u128 *V; static size_t n=0,cap=0; static int R=5;
static void push(u128 v){ if(n==cap){ cap=cap?cap*2:1<<16; V=realloc(V,cap*sizeof(u128)); } V[n++]=v; }
static u32 *primes; static size_t np=0;
static void sieve(u64 lim){ char *c=calloc(lim+1,1); for(u64 i=2;i<=lim;i++){ if(!c[i]){ primes=realloc(primes,(np+1)*sizeof(u32)); primes[np++]=(u32)i; for(u64 j=i*i;j<=lim;j+=i) c[j]=1; } } free(c); }
static void dfs(size_t i,u128 v){ push(v); for(size_t j=i;j<np;j++){ u128 p=primes[j],q=v; int ok=1; for(int e=0;e<R;e++){ if(q>N/p){ok=0;break;} q*=p; } if(!ok) break; while(1){ dfs(j+1,q); if(q>N/p) break; q*=p; } } }
static int cmp128(const void*a,const void*b){ u128 x=*(const u128*)a,y=*(const u128*)b; return x<y?-1:x>y; }
static u64 rng=88172645463325252ULL; static inline u64 xr(void){ rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; return rng; }
int main(int argc,char**argv){
    N=parse128(argv[1]); long samples=atol(argv[2]);
    u64 lim=(u64)pow((double)N,1.0/R)+2; sieve(lim); dfs(0,1); qsort(V,n,sizeof(u128),cmp128);
    fprintf(stderr,"n=%zu\n",n);
    // decade counts for density
    int K=40; double cnt[41]={0}; for(size_t i=0;i<n;i++){ double lg=log10((double)V[i]); int k=(int)floor(lg); if(k>=0&&k<=K) cnt[k]++; }
    // residue tables
    u32 mods[5]={32,243,3125,16807,161051}; double *rho[5];
    for(int t=0;t<5;t++){ rho[t]=calloc(mods[t],sizeof(double)); for(size_t i=0;i<n;i++) rho[t][(u32)(V[i]%mods[t])]+=1.0; for(u32 r=0;r<mods[t];r++) rho[t][r]*= (double)mods[t]/(double)n; }
    double expect[41]={0}; long got[41]={0};
    for(long s=0;s<samples;s++){
        size_t i=xr()%n,j=xr()%n,k=xr()%n; if(i==j||j==k||i==k) continue;
        u128 A=V[i],B=V[j],C=V[k]; u128 D=A+B+C; if(D>N) continue;
        if(gcd128(gcd128(A,B),C)!=1) continue;
        double Dd=(double)D; int dec=(int)floor(log10(Dd)); if(dec<0||dec>K) continue;
        double dens=cnt[dec]/(9.0*pow(10.0,dec));           // 5-full numbers per unit length in this decade
        double w=dens; for(int t=0;t<5;t++) w*=rho[t][(u32)(D%mods[t])];
        expect[dec]+=w; got[dec]++;
    }
    // total number of unordered triples of distinct elements
    double ntr=(double)n*(n-1.0)*(n-2.0)/6.0; double sampled=(double)samples/6.0; // each unordered triple sampled ~6 times per n^3 draws... we drew ordered with replacement
    // ordered draws with replacement: prob a given unordered triple is drawn in one draw = 6/n^3
    double scale=((double)n*n*n/6.0)/(double)samples;      // expected count = sum of weights * (#triples / #draws * 6/6)
    printf("decade  sampled_coprime_triples  expected_coprime_solutions\n");
    double tot=0;
    for(int k=8;k<=K;k++){ if(got[k]==0) continue; double e=expect[k]*scale; tot+=e; printf("1e%02d   %12ld   %10.4f\n",k,got[k],e); }
    printf("total expected (D<=N): %.4f   [observed: 2 for N>=2e12]\n",tot);
    return 0;
}
