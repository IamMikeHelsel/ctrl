/* AI-written local arithmetic experiment. No hardware or certified compiler claim. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <stdlib.h>
#define SCALE 10000
#define LIMIT 10000
#define ENERGY4 40000000LL
static int64_t quad(int64_t x, int64_t v) { return 5*x*x+2*x*v+v*v; }
static int64_t cell(int32_t x,int32_t v) {
  int64_t best=0;
  for(int sx=-1;sx<=1;sx+=2) for(int sv=-1;sv<=1;sv+=2) {
    int64_t q=quad(2*(int64_t)x+sx,2*(int64_t)v+sv);
    if(q>best) best=q;
  }
  return best;
}
static int32_t raw(int32_t x,int32_t v) { return -2*x-3*v; }
static int32_t clip(int32_t u) { return u>LIMIT?LIMIT:(u<-LIMIT?-LIMIT:u); }
/* Explicit modulo model; never invoke signed-overflow undefined behavior. */
static int64_t signed32(int64_t x) {
  uint32_t q=(uint32_t)(uint64_t)x;
  return q<=INT32_MAX?(int64_t)q:(int64_t)q-4294967296LL;
}
int main(int argc,char **argv) {
 if(argc==2 && strcmp(argv[1],"--sweep")==0) {
  int64_t admitted=0,point=0,point_only=0,total=0; int32_t peak=0;
  for(int32_t x=-1601;x<=1601;x++) for(int32_t v=-3601;v<=3601;v++) {
    int64_t q=cell(x,v); int safe=q<=ENERGY4;
    int center=quad(x,v)<=10000000LL;
    admitted+=safe;point+=center;point_only+=(center&&!safe);total++;
    if(safe) { int32_t u=raw(x,v);if(abs(u)>peak)peak=abs(u);if(u!=clip(u))return 3; }
  }
  printf("{\"total\":%"PRId64",\"admitted\":%"PRId64",\"point\":%"PRId64",\"point_only\":%"PRId64",\"peak_abs_raw\":%"PRId32"}\n",total,admitted,point,point_only,peak);
  return 0;
 }
 int32_t x,v;
 while(scanf("%"SCNd32" %"SCNd32,&x,&v)==2) {
  if(x<INT16_MIN||x>INT16_MAX||v<INT16_MIN||v>INT16_MAX) return 2;
  int64_t q=cell(x,v);int32_t u=raw(x,v);
  printf("%"PRId32" %"PRId32" %"PRId32" %"PRId32" %d %d %"PRId64" %d\n",x,v,u,clip(u),quad(x,v)<=10000000LL,q<=ENERGY4,q,signed32(q)<=ENERGY4);
 }
 return 0;
}
