#include <ruckig/ruckig.hpp>
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>

int main(int argc, char** argv) {
    try {
        if (argc < 5) throw std::runtime_error("usage: exporter p v a target [query_time ...]");
        ruckig::Ruckig<1> generator;
        ruckig::InputParameter<1> in;
        in.current_position = {std::stod(argv[1])};
        in.current_velocity = {std::stod(argv[2])};
        in.current_acceleration = {std::stod(argv[3])};
        in.target_position = {std::stod(argv[4])};
        in.target_velocity = {0.0}; in.target_acceleration = {0.0};
        in.max_velocity = {0.1}; in.max_acceleration = {0.5}; in.max_jerk = {7.5};
        const bool valid = generator.validate_input(in, false, true);
        if (!valid) throw std::runtime_error("input validation failed");
        ruckig::Trajectory<1> trajectory;
        const auto result = generator.calculate(in, trajectory);
        if (static_cast<int>(result) < 0) throw std::runtime_error("calculate error " + std::to_string(static_cast<int>(result)));
        const auto& profiles = trajectory.get_profiles();
        if (profiles.size() != 1) throw std::runtime_error("unexpected section count");
        const auto& p = profiles[0][0];
        if (p.accel.duration != 0.0) throw std::runtime_error("unsupported active accel profile");
        std::cout << std::setprecision(17);
        std::cout << "{\"result\":" << static_cast<int>(result) << ",\"input_valid\":true,\"duration\":" << trajectory.get_duration()
                  << ",\"brake_duration\":" << p.brake.duration << ",\"accel_duration\":" << p.accel.duration << ",\"phases\":[";
        bool comma = false;
        std::vector<double> boundaries{0.0, trajectory.get_duration()};
        auto phase = [&](const char* kind, int index, double start, double end, double duration, double native_t_sum, double jerk, double pos, double vel, double acc) {
            if (comma) std::cout << ','; comma = true;
            std::cout << "{\"kind\":\"" << kind << "\",\"index\":" << index << ",\"start\":" << start << ",\"end\":" << end << ",\"duration\":" << duration
                      << ",\"native_t_sum\":" << native_t_sum << ",\"jerk\":" << jerk << ",\"p\":" << pos << ",\"v\":" << vel << ",\"a\":" << acc << '}';
            if (duration > 0.0) { boundaries.push_back(start); boundaries.push_back(end); }
        };
        double brake_time=0.0;
        if (p.brake.duration > 0.0) {
            for (int i=0; i<2; ++i) {
                const double dt=p.brake.t[i];
                if (dt > 0.0) phase("brake", i, brake_time, brake_time+dt, dt, brake_time+dt, p.brake.j[i], p.brake.p[i], p.brake.v[i], p.brake.a[i]);
                else { if (comma) std::cout << ','; comma=true; std::cout << "{\"kind\":\"brake\",\"index\":" << i << ",\"start\":" << brake_time << ",\"duration\":" << dt << ",\"inactive_state_omitted\":true}"; }
                brake_time += dt;
            }
        } else {
            std::cout << "{\"kind\":\"brake\",\"duration\":0,\"inactive_arrays_omitted\":true}"; comma=true;
        }
        double start=p.brake.duration;
        for (int i=0; i<7; ++i) {
            phase("main", i, start, p.brake.duration+p.t_sum[i], p.t[i], p.t_sum[i], p.j[i], p.p[i], p.v[i], p.a[i]);
            start=p.brake.duration+p.t_sum[i];
        }
        std::cout << "],\"tail\":{\"start\":" << (p.brake.duration+p.t_sum.back())
                  << ",\"p\":" << p.p.back() << ",\"v\":" << p.v.back() << ",\"a\":" << p.a.back() << ",\"jerk\":0},\"samples\":[";
        std::sort(boundaries.begin(),boundaries.end());
        boundaries.erase(std::unique(boundaries.begin(),boundaries.end()),boundaries.end());
        std::vector<double> times=boundaries;
        for (double t: boundaries) { if(t>0)times.push_back(std::nextafter(t,0.0)); times.push_back(std::nextafter(t,std::numeric_limits<double>::infinity())); }
        for (size_t i=1;i<boundaries.size();++i) for(double f:{.25,.5,.75}) times.push_back(boundaries[i-1]+f*(boundaries[i]-boundaries[i-1]));
        times.push_back(trajectory.get_duration()+.01); times.push_back(trajectory.get_duration()+1.0);
        for(int i=5;i<argc;++i)times.push_back(std::stod(argv[i]));
        std::sort(times.begin(),times.end()); times.erase(std::unique(times.begin(),times.end()),times.end());
        comma=false;
        for(double t:times) {
            std::array<double,1> pos,vel,acc,j;size_t section;
            trajectory.at_time(t,pos,vel,acc,j,section);
            if(comma)std::cout<<',';comma=true;
            std::cout << "{\"t\":" << t << ",\"p\":" << pos[0] << ",\"v\":" << vel[0] << ",\"a\":" << acc[0] << ",\"jerk\":" << j[0] << ",\"section\":" << section << '}';
        }
        std::cout << "]}\n";
        return 0;
    } catch(const std::exception& error) { std::cerr << error.what() << '\n'; return 1; }
}
