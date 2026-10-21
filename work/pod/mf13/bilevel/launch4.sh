#!/bin/zsh
cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
./run.sh n7_local.py 0.1 3 80 0.02 > n7_local_a.log 2>&1 &
./run.sh n7_local.py 0.3 4 80 0.05 > n7_local_b.log 2>&1 &
./run.sh track_a.py 31 0.01 500 48 0.8 > runs_31.out 2>&1 &
wait
