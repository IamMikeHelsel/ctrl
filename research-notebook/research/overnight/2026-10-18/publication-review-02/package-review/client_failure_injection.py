"""Reviewer failure-path injection; never counts as a proof or kernel replay."""
from pathlib import Path
import sys,subprocess
R=Path(__file__).resolve().parent;P=R/'package-v3';sys.path.insert(0,str(P));import client
mode=sys.argv[1];output=R/'client-tests'/('injected-'+mode)
original_run=subprocess.run

def controlled_run(argv,*args,**kwargs):
    argv=[str(x) for x in argv]
    if mode=='kernel-nonzero' and Path(argv[0]).name=='leanchecker':
        return subprocess.CompletedProcess(argv,9,'Deliberate reviewer kernel failure. No kernel proof claimed.\n')
    result=original_run(argv,*args,**kwargs)
    if mode=='missing-axiom-audit' and '-o' in argv:
        assert result.returncode==0, result.stdout
        return subprocess.CompletedProcess(argv,0,'')
    return result
client.subprocess.run=controlled_run
sys.argv=['client.py','--input',str(P/'examples/on-time.json'),'--replay-output',str(R/'fresh-replay-v3'),'--output',str(output)]
client.main()
