#!/bin/zsh
cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
./run.sh landscape.py gauss 2000 101 > land_gauss_101.log 2>&1 &
./run.sh landscape.py fromA 2000 102 > land_fromA_102.log 2>&1 &
wait
