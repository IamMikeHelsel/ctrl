#include <algorithm>
#include <cmath>
#include <vector>

// Search only. These floating-point integrations are not proof certificates.
static void ad_rhs(double t, const double *y, double l, double u,
                   double rl, double ru, double *d) {
  const double f=(t-l)/(u-l), r=rl+(ru-rl)*f;
  d[0]=-.5*r*y[2];
  d[1]=40*y[0]-1.5*r*y[2];
  d[2]=40*y[1]-1.5*r*y[2];
  d[3]=r*y[2]/1600*(1-f);
  d[4]=r*y[2]/1600*f;
}
extern "C" double adverse(int n, const double *knots, const double *rate,
                           double target, int component, double max_step,
                           double *weights, double *zcoeff) {
  std::fill(weights,weights+n,0.0);
  double y[5]={0,0,0,0,0}; y[component]=component==1 ? 40000 : 80000;
  for(int j=n-2;j>=0;--j) {
    double l=knots[j],u=knots[j+1], top=std::min(u,target);
    if(top<=l) continue;
    y[3]=y[4]=0;
    int count=std::max(1,(int)std::ceil((top-l)/max_step));
    const double h=(top-l)/count;
    for(int q=0;q<count;++q) {
      const double t=top-q*h; double k1[5],k2[5],k3[5],k4[5],v[5];
      ad_rhs(t,y,l,u,rate[j],rate[j+1],k1);
      for(int k=0;k<5;++k)v[k]=y[k]+h*k1[k]/2;
      ad_rhs(t-h/2,v,l,u,rate[j],rate[j+1],k2);
      for(int k=0;k<5;++k)v[k]=y[k]+h*k2[k]/2;
      ad_rhs(t-h/2,v,l,u,rate[j],rate[j+1],k3);
      for(int k=0;k<5;++k)v[k]=y[k]+h*k3[k];
      ad_rhs(t-h,v,l,u,rate[j],rate[j+1],k4);
      for(int k=0;k<5;++k)y[k]+=h*(k1[k]+2*k2[k]+2*k3[k]+k4[k])/6;
    }
    weights[j]+=y[3]; weights[j+1]+=y[4];
  }
  zcoeff[0]=y[0]-y[1]+y[2]; zcoeff[1]=y[1]-2*y[2]; zcoeff[2]=y[2];
  double result=0;
  for(int k=0;k<3;++k)result+=.0002*std::abs(zcoeff[k]);
  for(int j=0;j<n;++j)result+=.01*std::abs(weights[j]);
  return result;
}
static void fw_rhs(double t,const double *y,double l,double u,
                   double rl,double ru,double wl,double wu,double *d) {
  const double f=(t-l)/(u-l),r=rl+(ru-rl)*f,w=wl+(wu-wl)*f;
  d[0]=40*y[1];d[1]=40*y[2];
  d[2]=r*(-.5*y[0]-1.5*y[1]-1.5*y[2]+w/1600);
}
extern "C" void forward(int n,const double *knots,const double *rate,
                         const double *dist,int m,const double *outtimes,
                         const double *initial,double max_step,double *states) {
  double y[3]={initial[0],initial[1],initial[2]},t=0;int j=0;
  for(int oi=0;oi<m;++oi) {
    const double target=outtimes[oi];
    while(t<target-1e-14) {
      while(j<n-2 && t>=knots[j+1]-1e-14)++j;
      const double h=std::min({max_step,target-t,knots[j+1]-t});
      double k1[3],k2[3],k3[3],k4[3],v[3];
      fw_rhs(t,y,knots[j],knots[j+1],rate[j],rate[j+1],dist[j],dist[j+1],k1);
      for(int k=0;k<3;++k)v[k]=y[k]+h*k1[k]/2;
      fw_rhs(t+h/2,v,knots[j],knots[j+1],rate[j],rate[j+1],dist[j],dist[j+1],k2);
      for(int k=0;k<3;++k)v[k]=y[k]+h*k2[k]/2;
      fw_rhs(t+h/2,v,knots[j],knots[j+1],rate[j],rate[j+1],dist[j],dist[j+1],k3);
      for(int k=0;k<3;++k)v[k]=y[k]+h*k3[k];
      fw_rhs(t+h,v,knots[j],knots[j+1],rate[j],rate[j+1],dist[j],dist[j+1],k4);
      for(int k=0;k<3;++k)y[k]+=h*(k1[k]+2*k2[k]+2*k3[k]+k4[k])/6;
      t+=h;
    }
    for(int k=0;k<3;++k)states[3*oi+k]=y[k];
  }
}
