#!/bin/zsh
cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
./run.sh track_a_gen.py 6 1 0.02 700 24 0.5 > runsAG6_1.out 2>&1 &
./run.sh track_a_gen.py 6 2 0.02 700 24 0.5 > runsAG6_2.out 2>&1 &
wait
