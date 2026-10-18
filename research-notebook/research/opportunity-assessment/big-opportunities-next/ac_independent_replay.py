"""Independent list-splice word reduction; does not import the official verifier."""
import json
from pathlib import Path
B=Path(__file__).resolve().parent
r=json.loads((B/'ac-probe.json').read_text())
def reduced(word):
    word=list(word)
    while True:
        for i in range(len(word)-1):
            if word[i]==-word[i+1]:
                del word[i:i+2];break
        else:return word
def inv(word):return [-x for x in word[::-1]]
state=[list(x) for x in r['initial_relators']]
trace=[state]
for move in r['path']:
    a,b=[list(x) for x in state]
    if move==0:a=inv(a)
    elif move==1:b=inv(b)
    elif move==2:a=a+b
    elif move==3:a=a+inv(b)
    elif move==4:b=b+a
    elif move==5:b=b+inv(a)
    elif 6<=move<=9:
        g=[1,-1,2,-2][move-6];a=[g]+a+[-g]
    elif 10<=move<=13:
        g=[1,-1,2,-2][move-10];b=[g]+b+[-g]
    else:raise ValueError(move)
    state=[reduced(a),reduced(b)];trace.append(state)
assert state==[[1],[2]]
out={'challenge_id':r['challenge_id'],'path':r['path'],'endpoint':state,
'trace':trace,'work':sum(sum(map(len,s)) for s in trace),
'peak_total_relator_length':max(sum(map(len,s)) for s in trace),
'local_exact_replay_passed':True,'shortest_or_new_claim':False,
'proof_scope':'Exact finite free-word calculation independently implemented in Python; no general AC soundness theorem or Lean kernel proof claimed.'}
(B/'ac-independent-replay.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['endpoint'],out['work'])
