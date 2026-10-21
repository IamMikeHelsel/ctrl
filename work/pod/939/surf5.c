// surf5.c -- integer points on the "Cohn surface" A X^5 + B Y^5 + C Z^5 = D W^5 attached to a known solution
// (A,B,C,D) of the r=5 problem.  Every integer point gives 5-full terms automatically (5-full * 5th power).
// Signed coordinates allowed: a point is a valid Erdos-939 solution iff exactly one of the four signed terms
// A X^5, B Y^5, C Z^5, -D W^5 has sign opposite to the other three (then that term is the "sum").
// MITM: {A X^5 + B Y^5} vs {D W^5 - C Z^5}, bucketed by residue mod M to bound memory.  128-bit signed.
// build: cc -O3 -march=native -o surf5 surf5.c -lpthread
// usage: ./surf5 A B C D H M nthreads
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>
typedef __int128 i128; typedef unsigned __int128 u128; typedef int64_t i64; typedef int32_t i32; typedef uint32_t u32;
static u128 parse128(const char *s){ u128 v=0; for(;*s;s++){ if(*s<'0'||*s>'9') break; v=v*10+(u128)(*s-'0'); } return v; }
static void print128(FILE *f, i128 v){ if(v<0){ fputc('-',f); v=-v; } char buf[64]; int i=63; buf[i]=0; if(v==0){ fputc('0',f); return;} while(v){ buf[--i]='0'+(int)(v%10); v/=10; } fputs(buf+i,f); }
static i64 gcd64(i64 a,i64 b){ if(a<0)a=-a; if(b<0)b=-b; while(b){ i64 t=a%b; a=b; b=t; } return a; }
static i128 A,B,C,D; static int H; static u32 M; static int nthreads;
static i128 *P5; // P5[x+H] = x^5
typedef struct { i128 v; i32 a,b; } ent;
static int cmpent(const void *p,const void *q){ i128 x=((const ent*)p)->v,y=((const ent*)q)->v; return x<y?-1:x>y; }
static inline u32 res(i128 v){ i128 r=v%(i128)M; if(r<0) r+=M; return (u32)r; }
static pthread_mutex_t mx=PTHREAD_MUTEX_INITIALIZER; static long nfound=0;
static void *worker(void *arg){
    long tid=(long)arg; ent *L=NULL,*R=NULL; size_t cl=0,cr=0,kl=0,kr=0;
    // precompute residues of A x^5 etc.
    u32 *rA=malloc((2*H+1)*4),*rB=malloc((2*H+1)*4),*rC=malloc((2*H+1)*4),*rD=malloc((2*H+1)*4);
    for(int x=-H;x<=H;x++){ rA[x+H]=res(A*P5[x+H]); rB[x+H]=res(B*P5[x+H]); rC[x+H]=res(C*P5[x+H]); rD[x+H]=res(D*P5[x+H]); }
    // index lists by residue for B y^5 and C z^5 (so we can enumerate pairs hitting bucket m fast)
    u32 *cntB=calloc(M+1,4),*cntC=calloc(M+1,4); for(int y=-H;y<=H;y++){ cntB[rB[y+H]+1]++; cntC[rC[y+H]+1]++; }
    for(u32 r=0;r<M;r++){ cntB[r+1]+=cntB[r]; cntC[r+1]+=cntC[r]; }
    i32 *idxB=malloc((2*H+1)*4),*idxC=malloc((2*H+1)*4); u32 *fb=calloc(M,4),*fc=calloc(M,4);
    for(int y=-H;y<=H;y++){ idxB[cntB[rB[y+H]]+fb[rB[y+H]]++]=y; idxC[cntC[rC[y+H]]+fc[rC[y+H]]++]=y; }
    for(u32 m=tid;m<M;m+=nthreads){
        cl=cr=0;
        for(int x=-H;x<=H;x++){ u32 need=(m+M-rA[x+H])%M; for(u32 t=cntB[need];t<cntB[need+1];t++){ int y=idxB[t]; if(cl==kl){ kl=kl?kl*2:1<<16; L=realloc(L,kl*sizeof(ent)); } L[cl].v=A*P5[x+H]+B*P5[y+H]; L[cl].a=x; L[cl].b=y; cl++; } }
        for(int w=-H;w<=H;w++){ u32 need=(rD[w+H]+M-m)%M; for(u32 t=cntC[need];t<cntC[need+1];t++){ int z=idxC[t]; if(cr==kr){ kr=kr?kr*2:1<<16; R=realloc(R,kr*sizeof(ent)); } R[cr].v=D*P5[w+H]-C*P5[z+H]; R[cr].a=z; R[cr].b=w; cr++; } }
        qsort(L,cl,sizeof(ent),cmpent); qsort(R,cr,sizeof(ent),cmpent);
        size_t p=0,q=0;
        while(p<cl&&q<cr){ if(L[p].v<R[q].v) p++; else if(L[p].v>R[q].v) q++; else { i128 v=L[p].v; size_t p2=p,q2=q; while(p2<cl&&L[p2].v==v) p2++; while(q2<cr&&R[q2].v==v) q2++;
            for(size_t a=p;a<p2;a++) for(size_t b=q;b<q2;b++){ int x=L[a].a,y=L[a].b,z=R[b].a,w=R[b].b;
                if(x==0&&y==0&&z==0&&w==0) continue;
                i64 g=gcd64(gcd64(x,y),gcd64(z,w)); if(g!=1) continue;      // primitive only
                if(x==y&&y==z&&z==w) continue;                               // the known point
                i128 T[4]={A*P5[x+H],B*P5[y+H],C*P5[z+H],-D*P5[w+H]}; int neg=0,zero=0; for(int i=0;i<4;i++){ if(T[i]<0) neg++; if(T[i]==0) zero++; }
                const char *tag = zero? "ZERO" : ((neg==1||neg==3)? "VALID3+1" : "TWO+TWO");
                pthread_mutex_lock(&mx); nfound++;
                printf("%s X=%d Y=%d Z=%d W=%d  terms:",tag,x,y,z,w); for(int i=0;i<4;i++){ putchar(' '); print128(stdout,T[i]); } putchar('\n'); fflush(stdout);
                pthread_mutex_unlock(&mx); }
            p=p2; q=q2; } }
        if(tid==0&&(m/nthreads)%64==0) fprintf(stderr,"bucket %u/%u |L|=%zu |R|=%zu found=%ld\n",m,M,cl,cr,nfound);
    }
    return NULL;
}
int main(int argc,char**argv){
    if(argc<8){ fprintf(stderr,"usage: %s A B C D H M nthreads\n",argv[0]); return 1; }
    A=(i128)parse128(argv[1]); B=(i128)parse128(argv[2]); C=(i128)parse128(argv[3]); D=(i128)parse128(argv[4]); H=atoi(argv[5]); M=atoi(argv[6]); nthreads=atoi(argv[7]);
    P5=malloc((2*H+1)*sizeof(i128)); for(int x=-H;x<=H;x++){ i128 v=x; v=v*v*v*v*v; P5[x+H]=v; }
    fprintf(stderr,"surface: "); print128(stderr,A); fprintf(stderr," X^5 + "); print128(stderr,B); fprintf(stderr," Y^5 + "); print128(stderr,C); fprintf(stderr," Z^5 = "); print128(stderr,D); fprintf(stderr," W^5,  |coords|<=%d\n",H);
    pthread_t th[64]; for(long t=0;t<nthreads;t++) pthread_create(&th[t],NULL,worker,(void*)t); for(long t=0;t<nthreads;t++) pthread_join(th[t],NULL);
    fprintf(stderr,"DONE H=%d found=%ld\n",H,nfound); return 0;
}
