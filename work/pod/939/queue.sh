#!/bin/zsh
cd /Users/mike/Dev/ctrl/work/pod/939
while pgrep -f 'mitm5 100000000000000000000 ' >/dev/null; do sleep 20; done
echo "[queue] $(date) mitm5 1e20 done: $(tail -1 runs/mitm5_1e20.err)" >> runs/queue.log
echo "[queue] $(date) start surf5 H=40000 (both surfaces, 2 threads each)" >> runs/queue.log
./surf5 772402208 1977326743 134481277728 137231006679 40000 65521 2 > runs/surf5_kitamura_H40000.log 2> runs/surf5_kitamura_H40000.err &
./surf5 1180980000000 606355001344 59797108943 1847132110287 40000 65521 2 > runs/surf5_cambie_H40000.log 2> runs/surf5_cambie_H40000.err &
wait
echo "[queue] $(date) surf5 done: $(tail -1 runs/surf5_kitamura_H40000.err) / $(tail -1 runs/surf5_cambie_H40000.err)" >> runs/queue.log
echo "[queue] $(date) start full4 1e20" >> runs/queue.log
./full4 100000000000000000000 4 > runs/full4_1e20.out 2> runs/full4_1e20.err
echo "[queue] $(date) done full4 1e20: $(tail -1 runs/full4_1e20.err)" >> runs/queue.log
echo "[queue] $(date) start mitm5 1e22" >> runs/queue.log
./mitm5 10000000000000000000000 16381 4 > runs/mitm5_1e22.out 2> runs/mitm5_1e22.err
echo "[queue] $(date) done mitm5 1e22: $(tail -1 runs/mitm5_1e22.err)" >> runs/queue.log
