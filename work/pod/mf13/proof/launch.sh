#!/bin/zsh
# usage: launch.sh LOGNAME script args...   (new session via setsid; appends EXIT status)
cd /Users/mike/dev/ctrl/work/pod/mf13/proof
name=$1; shift
python3 -c "import os,sys; os.setsid(); os.execvp('zsh',['zsh','-c',sys.argv[1]])" "./pfx.sh $* > logs/$name.log 2>&1; echo EXIT \$? >> logs/$name.log" > /dev/null 2>&1 < /dev/null &
disown
