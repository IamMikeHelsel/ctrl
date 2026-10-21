#!/bin/zsh
cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
./run.sh track_a.py 1 0.02 600 16 0.5 > runs_1.out 2>&1 &
./run.sh track_a.py 2 0.05 600 16 0.5 > runs_2.out 2>&1 &
./run.sh track_a.py 3 0.1 600 16 0.5 > runs_3.out 2>&1 &
./run.sh track_b.py 11 1 0.05 600 16 0.5 > runs_11.out 2>&1 &
./run.sh track_b.py 12 2 0.05 600 16 0.5 > runs_12.out 2>&1 &
./run.sh track_b.py 13 3 0.05 600 16 0.5 > runs_13.out 2>&1 &
wait
