#!/bin/zsh
cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
./run.sh track_a_gen.py 7 1 0.02 600 24 0.5 > runsAG_1.out 2>&1 &
./run.sh track_a_gen.py 7 2 0.02 600 24 0.5 > runsAG_2.out 2>&1 &
wait
