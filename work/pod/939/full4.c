// full4.c -- exhaustive search for a+b=c with a,b,c 4-full, gcd(a,b)=1, c<=N.
// Hash-set membership on all 4-full numbers <= N; residue prefilter mod 2^4*3^4*5^4.
// build: cc -O3 -march=native -o full4 full4.c -lpthread
// usage: ./full4 N_decimal nthreads [r]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
typedef unsigned __int128 u128; typedef uint64_t u64; typedef uint32_t u32;
static u128 parse128(const char *s){ u128 v=0; for(;*s;s++){ if(*s<'0'||*s>'9') break; v=v*10+(u128)(*s-'0'); } return v; }
static void print128(FILE *f, u128 v){ char buf[64]; int i=63; buf[i]=0; if(v==0){ fputc('0',f); return;} while(v){ buf[--i]='0'+(int)(v%10); v/=10; } fputs(buf+i,f); }
static u128 gcd128(u128 a,u128 b){ while(b){ u128 t=a%b; a=b; b=t; } return a; }
static int R=4; static u128 N; static u128 *V; static size_t n=0,cap=0;
static void push(u128 v){ if(n==cap){ cap=cap?cap*2:1<<16; V=realloc(V,cap*sizeof(u128)); } V[n++]=v; }
static u32 *primes; static size_t np=0;
static void sieve(u64 lim){ char *c=calloc(lim+1,1); for(u64 i=2;i<=lim;i++){ if(!c[i]){ primes=realloc(primes,(np+1)*sizeof(u32)); primes[np++]=(u32)i; for(u64 j=i*i;j<=lim;j+=i) c[j]=1; } } free(c); }
static void dfs(size_t i,u128 v){ push(v); for(size_t j=i;j<np;j++){ u128 p=primes[j],q=v; int ok=1; for(int e=0;e<R;e++){ if(q>N/p){ok=0;break;} q*=p; } if(!ok) break; while(1){ dfs(j+1,q); if(q>N/p) break; q*=p; } } }
static int cmp128(const void*a,const void*b){ u128 x=*(const u128*)a,y=*(const u128*)b; return x<y?-1:x>y; }
// hash set
static u128 *H; static u64 hmask;
static inline u64 hsh(u128 x){ u64 a=(u64)x,b=(u64)(x>>64); a^=b*0x9E3779B97F4A7C15ULL; a*=0xBF58476D1CE4E5B9ULL; a^=a>>31; return a; }
static void hins(u128 x){ u64 h=hsh(x)&hmask; while(H[h]) h=(h+1)&hmask; H[h]=x; }
static inline int hhas(u128 x){ u64 h=hsh(x)&hmask; while(H[h]){ if(H[h]==x) return 1; h=(h+1)&hmask; } return 0; }
// residue filter
#define MOD (16*81*625)
static char allowed[MOD];
static void mkfilter(void){ // r-full residues mod p^r for p=2,3,5: either coprime to p or 0 mod p^r (for R=4)
    for(u32 x=0;x<MOD;x++){ int ok=1; u32 ms[3]={16,81,625}; u32 ps[3]={2,3,5}; for(int k=0;k<3;k++){ u32 m=ms[k],p=ps[k]; u32 rr=x%m; if(rr%p==0 && rr!=0) ok=0; } allowed[x]=ok; }
}
static int nthreads; static pthread_mutex_t mx=PTHREAD_MUTEX_INITIALIZER; static volatile long nsol=0,nnon=0;
static void *worker(void *arg){ long tid=(long)arg;
    for(size_t i=tid;i<n;i+=nthreads){ u128 a=V[i]; if(a==0) continue; u128 lim=N-a; u32 am=(u32)(a%MOD);
        for(size_t j=i+1;j<n && V[j]<=lim;j++){ u128 b=V[j]; u32 sm=am+(u32)(b%MOD); if(sm>=MOD) sm-=MOD; if(!allowed[sm]) continue; u128 c=a+b; if(hhas(c)){ u128 g=gcd128(a,b); pthread_mutex_lock(&mx); if(g==1){ nsol++; fputs("SOL4 ",stdout); print128(stdout,a); fputc(' ',stdout); print128(stdout,b); fputc(' ',stdout); print128(stdout,c); fputc('\n',stdout); fflush(stdout);} else nnon++; pthread_mutex_unlock(&mx);} }
        if(tid==0 && i%(4096*nthreads)==0){ fprintf(stderr,"i=%zu/%zu sol=%ld non=%ld\n",i,n,nsol,nnon); }
    }
    return NULL; }
int main(int argc,char**argv){ if(argc<3){fprintf(stderr,"usage: %s N nthreads [r]\n",argv[0]);return 1;} N=parse128(argv[1]); nthreads=atoi(argv[2]); if(argc>3) R=atoi(argv[3]);
    if(R!=4){ fprintf(stderr,"residue filter hardcoded for r=4\n"); }
    u64 lim=(u64)(__builtin_pow((double)N,1.0/R))+2; sieve(lim); dfs(0,1); qsort(V,n,sizeof(u128),cmp128);
    fprintf(stderr,"N="); print128(stderr,N); fprintf(stderr,"  %d-full count n=%zu\n",R,n);
    u64 hs=1; while(hs<4*n) hs<<=1; H=calloc(hs,sizeof(u128)); hmask=hs-1; for(size_t i=0;i<n;i++) if(V[i]) hins(V[i]);
    mkfilter();
    pthread_t th[256]; for(long t=0;t<nthreads;t++) pthread_create(&th[t],NULL,worker,(void*)t); for(long t=0;t<nthreads;t++) pthread_join(th[t],NULL);
    fprintf(stderr,"DONE4 N="); print128(stderr,N); fprintf(stderr," n=%zu sol=%ld non=%ld\n",n,nsol,nnon); return 0; }
