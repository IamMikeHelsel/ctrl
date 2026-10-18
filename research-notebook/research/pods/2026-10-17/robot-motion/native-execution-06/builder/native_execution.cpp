// Primary retained history: all state carries and trajectory exports are native.
// stdin: commit count, then binary-round-trip time/target pairs.
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
struct Plan { double time,target; std::array<double,1> p,v,a; ruckig::Trajectory<1> trajectory; int result; };
int main(int argc,char** argv) {
 try {
    if(argc!=3)throw std::runtime_error("usage: native_execution minimum_duration horizon");
    const double minimum_duration=std::stod(argv[1]), horizon=std::stod(argv[2]);
    size_t n;if(!(std::cin>>n)||n==0)throw std::runtime_error("invalid commit count");
    std::vector<std::pair<double,double>> commits(n);
    for(auto& c:commits)if(!(std::cin>>c.first>>c.second))throw std::runtime_error("invalid commit input");
    ruckig::Ruckig<1> generator;std::vector<Plan> plans;
    std::array<double,1> p{0.},v{0.},a{0.};
    for(const auto& c:commits) {
       if(!plans.empty()) {
          if(c.first<=plans.back().time)throw std::runtime_error("non-increasing native clock");
          plans.back().trajectory.at_time(c.first-plans.back().time,p,v,a);
       }
       ruckig::InputParameter<1> input;input.current_position=p;input.current_velocity=v;input.current_acceleration=a;
       input.target_position={c.second};input.target_velocity={0.};input.target_acceleration={0.};
       input.max_velocity={.1};input.max_acceleration={.5};input.max_jerk={7.5};
       if(minimum_duration>0.)input.minimum_duration=minimum_duration;
       Plan plan;plan.time=c.first;plan.target=c.second;plan.p=p;plan.v=v;plan.a=a;
       if(!generator.validate_input(input,false,true))throw std::runtime_error("invalid native input");
       plan.result=static_cast<int>(generator.calculate(input,plan.trajectory));
       if(plan.result<0)throw std::runtime_error("native calculation failed");
       plans.push_back(plan);
    }
    std::cout<<std::setprecision(17)<<"{\"minimum_duration\":"<<minimum_duration<<",\"clock\":\"native double absolute commits and native subtraction; state retained by at_time\",\"plans\":[";
    bool comma=false;
    for(size_t i=0;i<plans.size();++i) {
      const auto& plan=plans[i];
      const double next=i+1<plans.size()?plans[i+1].time:horizon;
      const double elapsed=next-plan.time;
      if(comma)std::cout<<',';comma=true;
      std::cout<<"{\"native_commit\":"<<plan.time<<",\"target\":"<<plan.target<<",\"current_state\":["<<plan.p[0]<<','<<plan.v[0]<<','<<plan.a[0]<<"],\"native_elapsed_to_next_commit_or_horizon\":"<<elapsed<<",\"plan\":";
      emit_profile(plan.trajectory,plan.result,minimum_duration,{elapsed});
      std::cout<<'}';
    }
    std::cout<<"]}\n";
 } catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}
}
