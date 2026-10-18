// Diagnostic only: build the retained Ruckig history entirely with native at_time.
// stdin: number of commits, then time/target pairs, then query count and times.
#include <ruckig/ruckig.hpp>
#include <algorithm>
#include <array>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <vector>
struct Plan { double time,target; std::array<double,1> p,v,a; ruckig::Trajectory<1> trajectory; int result; };
int main(int argc,char** argv) {
 try {
    const double minimum_duration=argc>1?std::stod(argv[1]):0.;
    size_t n; if(!(std::cin>>n))return 1;
    std::vector<std::pair<double,double>> commits(n);for(auto& c:commits)if(!(std::cin>>c.first>>c.second))throw std::runtime_error("invalid commit input");
    size_t m;if(!(std::cin>>m))throw std::runtime_error("invalid query count");std::vector<double> queries(m);for(double& t:queries)if(!(std::cin>>t))throw std::runtime_error("invalid query time");
    ruckig::Ruckig<1> generator;std::vector<Plan> plans;
    std::array<double,1> p{0.},v{0.},a{0.};
    for(const auto& c:commits) {
       if(!plans.empty())plans.back().trajectory.at_time(c.first-plans.back().time,p,v,a);
       ruckig::InputParameter<1> input;input.current_position=p;input.current_velocity=v;input.current_acceleration=a;
       input.target_position={c.second};input.target_velocity={0.};input.target_acceleration={0.};
       input.max_velocity={.1};input.max_acceleration={.5};input.max_jerk={7.5};
       if(minimum_duration>0.)input.minimum_duration=minimum_duration;
       Plan plan;plan.time=c.first;plan.target=c.second;plan.p=p;plan.v=v;plan.a=a;
       if(!generator.validate_input(input,false,true))throw std::runtime_error("invalid native replay input");
       plan.result=static_cast<int>(generator.calculate(input,plan.trajectory));
       if(plan.result<0)throw std::runtime_error("native replay calculation failed");
       plans.push_back(plan);
    }
    std::cout<<std::setprecision(17)<<"{\"minimum_duration\":"<<minimum_duration<<",\"clock\":\"native double absolute times and native subtraction\",\"commits\":[";
    bool comma=false;
    for(const auto& plan:plans) {
      if(comma)std::cout<<',';comma=true;
      std::cout<<"{\"time\":"<<plan.time<<",\"target\":"<<plan.target<<",\"current_p\":"<<plan.p[0]<<",\"current_v\":"<<plan.v[0]<<",\"current_a\":"<<plan.a[0]<<",\"duration\":"<<plan.trajectory.get_duration()<<",\"result\":"<<plan.result<<'}';
    }
    std::cout<<"],\"queries\":[";comma=false;
    for(double t:queries) {
      std::array<double,1> qp{0.},qv{0.},qa{0.},j{0.};size_t section=0;
      auto after=std::upper_bound(plans.begin(),plans.end(),t,[](double time,const Plan& plan){return time<plan.time;});
      if(after!=plans.begin()){--after;after->trajectory.at_time(t-after->time,qp,qv,qa,j,section);}
      if(comma)std::cout<<',';comma=true;
      std::cout<<"{\"time\":"<<t<<",\"q\":"<<qp[0]<<",\"qv\":"<<qv[0]<<",\"qa\":"<<qa[0]<<",\"jerk\":"<<j[0]<<'}';
    }
    std::cout<<"]}\n";
 } catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}
}
