"""Bounded local exact path search. Never uploads or claims global optimality."""
import sys,json,time
from pathlib import Path
base=Path(__file__).resolve().parent
sys.path.insert(0,str(base/'andrews-curtis/competition/tools'))
from verifier.core import apply_move,INVERSE_MOVE,verify,MOVE_SPEC_VERSION
m=json.loads((base/'andrews-curtis/competition/tools/verifier/data/manifest.json').read_text())
c=next(c for c in m['challenges'] if c['challenge_id']=='ac-08491')
start=tuple(map(tuple,c['initial_relators'])); target=((1,),(2,))
t0=time.monotonic(); limit=t0+60
reverse={target:()}; frontier=[target]
for depth in range(5):
    nxt=[]
    for s in frontier:
        for move in range(14):
            v=apply_move(s,move)
            if v not in reverse and sum(map(len,v))<=24:
                reverse[v]=(INVERSE_MOVE[move],)+reverse[s];nxt.append(v)
    frontier=nxt
    if len(reverse)>150000 or time.monotonic()>limit:break
visited={start};beam=[(start,())];found=None;expanded=0
for depth in range(50):
    options=[]
    for s,path in beam:
        if s in reverse:
            found=path+reverse[s];break
        for move in range(14):
            v=apply_move(s,move);expanded+=1
            if v in visited or sum(map(len,v))>40:continue
            visited.add(v)
            np=path+(move,)
            if v in reverse:
                found=np+reverse[v];break
            options.append((v,np))
        if found or time.monotonic()>limit:break
    if found or time.monotonic()>limit or not options:break
    options.sort(key=lambda x:(sum(map(len,x[0])),max(map(len,x[0])),x[0]))
    beam=options[:2000]
result={'challenge_id':c['challenge_id'],'initial_relators':c['initial_relators'],
'seconds':time.monotonic()-t0,'reverse_states':len(reverse),'forward_states':len(visited),
'expanded_moves':expanded,'beam_width':2000,'forward_depth_reached':depth,'limit_seconds':60,
'path':list(found) if found else None,'global_shortest_or_novel':False}
if found:
    result['reference_verifier']=verify(c,list(found),MOVE_SPEC_VERSION,m['limits'])
    (base/'ac-local-certificate.txt').write_text(f"{c['challenge_id']}: {list(found)}\n")
(base/'ac-probe.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
