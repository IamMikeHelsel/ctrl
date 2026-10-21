// mitm5.c -- exhaustive meet-in-the-middle search for A+B+C=D with all four 5-full, D<=N.
// No coprimality pruning (so it also covers the "all pairwise gcds>1" case Cambie's MITM skipped).
// Residue bucketing mod M keeps memory ~ n^2/M. 128-bit arithmetic.  pthreads over buckets.
//
// build: cc -O3 -march=native -o mitm5 mitm5.c -lpthread
// usage: ./mitm5 N_decimal M nthreads [r]     (r defaults to 5; r=4 also handled below as A+B+C=D is not the r=4 problem,
//        so for r=4 use mitm4.c instead)
// output: lines "SOL A B C D g" (g = gcd(A,B,C)); "DUP ..." when C in {A,B}.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef uint32_t u32;

static u128 parse128(const char *s){ u128 v=0; for(;*s;s++){ if(*s<'0'||*s>'9') break; v=v*10+(u128)(*s-'0'); } return v; }
static void print128(FILE *f, u128 v){ char buf[64]; int i=63; buf[i]=0; if(v==0){ fputc('0',f); return;} while(v){ buf[--i]='0'+(int)(v%10); v/=10; } fputs(buf+i,f); }
static u128 gcd128(u128 a,u128 b){ while(b){ u128 t=a%b; a=b; b=t; } return a; }

static int R = 5;
static u128 N;
static u128 *V; static size_t n=0, cap=0;
static void push(u128 v){ if(n==cap){ cap=cap?cap*2:1<<16; V=realloc(V,cap*sizeof(u128)); } V[n++]=v; }

static u32 *primes; static size_t np=0;
static void sieve(u64 lim){ char *c=calloc(lim+1,1); for(u64 i=2;i<=lim;i++){ if(!c[i]){ primes=realloc(primes,(np+1)*sizeof(u32)); primes[np++]=(u32)i; for(u64 j=i*i;j<=lim;j+=i) c[j]=1; } } free(c); }

static void dfs(size_t i, u128 v){
    push(v);
    for(size_t j=i;j<np;j++){
        u128 p=primes[j], q=v;
        int ok=1;
        for(int e=0;e<R;e++){ if(q > N/p){ ok=0; break;} q*=p; }
        if(!ok) break;            // primes are increasing: p^R*v > N for all larger p too
        while(1){ dfs(j+1,q); if(q > N/p) break; q*=p; }
    }
}

static int cmp128(const void *a,const void *b){ u128 x=*(const u128*)a,y=*(const u128*)b; return x<y?-1:x>y; }

typedef struct { u128 s; u32 i,j; } ent;
static int cmpent(const void *a,const void *b){ u128 x=((const ent*)a)->s,y=((const ent*)b)->s; return x<y?-1:x>y; }

static u32 M; static u32 *cls_start, *cls_idx; // indices grouped by residue
static int nthreads; static pthread_mutex_t outmx=PTHREAD_MUTEX_INITIALIZER; static FILE *out;
static volatile long nsol=0, ndup=0, nnoncop=0;

static void addpairs(ent **buf,size_t *cnt,size_t *cap_,u128 s,u32 i,u32 j){
    if(*cnt==*cap_){ *cap_=*cap_?*cap_*2:1<<20; *buf=realloc(*buf,*cap_*sizeof(ent)); }
    (*buf)[*cnt].s=s; (*buf)[*cnt].i=i; (*buf)[*cnt].j=j; (*cnt)++;
}

static void *worker(void *arg){
    long tid=(long)arg;
    ent *S1=NULL,*S2=NULL; size_t c1=0,c2=0,k1=0,k2=0;
    for(u32 m=tid; m<M; m+=nthreads){
        c1=c2=0;
        // S1: A+B == m (mod M), A<B
        for(u32 r1=0;r1<M;r1++){
            u32 r2=(m+M-r1)%M; if(r1>r2) continue;
            u32 a0=cls_start[r1],a1=cls_start[r1+1],b0=cls_start[r2],b1=cls_start[r2+1];
            if(r1==r2){ for(u32 x=a0;x<a1;x++) for(u32 y=x+1;y<a1;y++){ u32 i=cls_idx[x],j=cls_idx[y]; u128 s=V[i]+V[j]; if(s>N) continue; if(V[i]<V[j]) addpairs(&S1,&c1,&k1,s,i,j); else addpairs(&S1,&c1,&k1,s,j,i);} }
            else { for(u32 x=a0;x<a1;x++) for(u32 y=b0;y<b1;y++){ u32 i=cls_idx[x],j=cls_idx[y]; u128 s=V[i]+V[j]; if(s>N) continue; if(V[i]<V[j]) addpairs(&S1,&c1,&k1,s,i,j); else addpairs(&S1,&c1,&k1,s,j,i);} }
        }
        // S2: D-C == m (mod M), C<D
        for(u32 rc=0;rc<M;rc++){
            u32 rd=(rc+m)%M;
            u32 a0=cls_start[rc],a1=cls_start[rc+1],b0=cls_start[rd],b1=cls_start[rd+1];
            for(u32 x=a0;x<a1;x++) for(u32 y=b0;y<b1;y++){ u32 i=cls_idx[x],j=cls_idx[y]; if(V[j]>V[i]) addpairs(&S2,&c2,&k2,V[j]-V[i],i,j); }
        }
        qsort(S1,c1,sizeof(ent),cmpent); qsort(S2,c2,sizeof(ent),cmpent);
        size_t p=0,q=0;
        while(p<c1&&q<c2){
            if(S1[p].s<S2[q].s) p++; else if(S1[p].s>S2[q].s) q++;
            else { u128 s=S1[p].s; size_t p2=p,q2=q; while(p2<c1&&S1[p2].s==s) p2++; while(q2<c2&&S2[q2].s==s) q2++;
                for(size_t a=p;a<p2;a++) for(size_t b=q;b<q2;b++){
                    u128 A=V[S1[a].i],B=V[S1[a].j],C=V[S2[b].i],D=V[S2[b].j];
                    pthread_mutex_lock(&outmx);
                    if(C==A||C==B){ ndup++; }
                    else { u128 g=gcd128(gcd128(A,B),C); if(g==1){ nsol++; fputs("SOL ",out);
                    print128(out,A); fputc(' ',out); print128(out,B); fputc(' ',out); print128(out,C); fputc(' ',out); print128(out,D); fputc('\n',out); fflush(out);} else { nnoncop++; } }
                    pthread_mutex_unlock(&outmx);
                }
                p=p2; q=q2; }
        }
        if(tid==0 && (m/nthreads)%16==0){ fprintf(stderr,"bucket %u/%u  |S1|=%zu |S2|=%zu  sol=%ld dup=%ld noncop=%ld\n",m,M,c1,c2,nsol,ndup,nnoncop); }
    }
    free(S1); free(S2); return NULL;
}

int main(int argc,char **argv){
    if(argc<4){ fprintf(stderr,"usage: %s N M nthreads [r]\n",argv[0]); return 1; }
    N=parse128(argv[1]); M=atoi(argv[2]); nthreads=atoi(argv[3]); if(argc>4) R=atoi(argv[4]);
    out=stdout;
    // prime limit: N^(1/R)
    double Nd=(double)N; u64 lim=(u64)(__builtin_pow(Nd,1.0/R))+2; sieve(lim);
    dfs(0,1);
    qsort(V,n,sizeof(u128),cmp128);
    fprintf(stderr,"N="); print128(stderr,N); fprintf(stderr,"  %d-full count n=%zu (primes<=%llu: %zu)\n",R,n,(unsigned long long)lim,np);
    // classes
    cls_start=calloc(M+1,sizeof(u32)); cls_idx=malloc(n*sizeof(u32));
    u32 *res=malloc(n*sizeof(u32)); for(size_t i=0;i<n;i++){ res[i]=(u32)(V[i]%M); cls_start[res[i]+1]++; }
    for(u32 r=0;r<M;r++) cls_start[r+1]+=cls_start[r];
    u32 *fill=calloc(M,sizeof(u32)); for(size_t i=0;i<n;i++){ cls_idx[cls_start[res[i]]+fill[res[i]]++]=(u32)i; }
    pthread_t th[256]; for(long t=0;t<nthreads;t++) pthread_create(&th[t],NULL,worker,(void*)t);
    for(long t=0;t<nthreads;t++) pthread_join(th[t],NULL);
    fprintf(stderr,"DONE N="); print128(stderr,N); fprintf(stderr," n=%zu sol=%ld dup=%ld noncop=%ld\n",n,nsol,ndup,nnoncop);
    return 0;
}
