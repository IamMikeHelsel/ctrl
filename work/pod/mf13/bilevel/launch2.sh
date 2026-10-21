#!/bin/zsh
cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
./run.sh track_fromA.py 1 6 800 24 0.5 none > runsFA_1.out 2>&1 &
./run.sh track_fromA.py 2 6 800 24 0.3 none > runsFA_2.out 2>&1 &
./run.sh track_fromA.py 3 6 800 24 0.5 blk33 > runsFA_3.out 2>&1 &
./run.sh track_fromA.py 1 7 800 24 0.5 none > runsFA_4.out 2>&1 &
./run.sh track_fromA.py 2 7 800 24 0.5 none > runsFA_5.out 2>&1 &
./run.sh track_a.py 21 0.01 800 32 1.0 > runs_21.out 2>&1 &
wait
