#include <ruckig/ruckig.hpp>
#include <algorithm>
#include <array>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>
#include "profile_export.hpp"
int main(int argc,char**argv) {
 try {
  if(argc!=2)throw std::runtime_error("usage native_suffix minimum_duration");
  double p,v,a,target; if(!(std::cin>>p>>v>>a>>target))throw std::runtime_error("invalid input");
  size_t n;if(!(std::cin>>n))throw std::runtime_error("missing query count");
  std::vector<double> queries(n);for(double& t:queries)if(!(std::cin>>t))throw std::runtime_error("invalid query");
  double minimum=std::stod(argv[1]);ruckig::Ruckig<1> generator;ruckig::InputParameter<1> input;ruckig::Trajectory<1> traj;
  input.current_position={p};input.current_velocity={v};input.current_acceleration={a};
  input.target_position={target};input.target_velocity={0};input.target_acceleration={0};
  input.max_velocity={.1};input.max_acceleration={.5};input.max_jerk={7.5};if(minimum>0)input.minimum_duration=minimum;
  bool valid=generator.validate_input(input,false,true);
  if(!valid){std::cout<<"{\"accepted\":false,\"reason\":\"invalid native input\"}\n";return 0;}
  int result=static_cast<int>(generator.calculate(input,traj));
  if(result<0){std::cout<<"{\"accepted\":false,\"result\":"<<result<<"}\n";return 0;}
  std::cout<<"{\"accepted\":true,\"plan\":";emit_profile(traj,result,minimum,queries);std::cout<<"}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}
}
