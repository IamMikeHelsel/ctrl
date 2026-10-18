#include <ruckig/ruckig.hpp>
#include <array>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <vector>
int main(int argc,char**argv) {
 try {
  if(argc!=2)throw std::runtime_error("usage native_queries minimum_duration");
  double p,v,a,target;size_t n; if(!(std::cin>>p>>v>>a>>target>>n))throw std::runtime_error("input");
  std::vector<double> queries(n);for(double&t:queries)if(!(std::cin>>t))throw std::runtime_error("query");
  ruckig::InputParameter<1> input;input.current_position={p};input.current_velocity={v};input.current_acceleration={a};input.target_position={target};input.target_velocity={0};input.target_acceleration={0};input.max_velocity={.1};input.max_acceleration={.5};input.max_jerk={7.5};double minimum=std::stod(argv[1]);if(minimum>0)input.minimum_duration=minimum;
  ruckig::Ruckig<1> generator;ruckig::Trajectory<1> traj;if(!generator.validate_input(input,false,true))throw std::runtime_error("invalid");int result=static_cast<int>(generator.calculate(input,traj));if(result<0)throw std::runtime_error("calculation failed");
  std::cout<<std::setprecision(17)<<"{\"duration\":"<<traj.get_duration()<<",\"queries\":[";bool comma=false;
  for(double t:queries){std::array<double,1> q,vv,aa,j;size_t section;traj.at_time(t,q,vv,aa,j,section);if(comma)std::cout<<',';comma=true;std::cout<<"{\"t\":"<<t<<",\"p\":"<<q[0]<<",\"v\":"<<vv[0]<<",\"a\":"<<aa[0]<<",\"jerk\":"<<j[0]<<"}";}
  std::cout<<"]}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}
}
