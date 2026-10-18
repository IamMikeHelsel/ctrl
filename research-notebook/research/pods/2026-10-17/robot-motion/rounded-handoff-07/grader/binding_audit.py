#!/usr/bin/env python3
"""Independent exact coefficient, duration and transformed-join audit; no ODE run."""
from fractions import Fraction as F
from pathlib import Path
import hashlib, json
from datetime import datetime, timezone
import re

HERE=Path(__file__).resolve().parent
NATIVE=HERE.parent.parent/'native-execution-06/builder'
BIND=HERE.parent/'bindings'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def matrix(d):
    # Independently written linear map; dimensions are metres in every row.
    M=((F(1),F(0),F(0)),(F(1),F(1,40),F(0)),(F(1),F(1,20),F(1,1600)))
    return tuple(sum(a*b for a,b in zip(row,d)) for row in M)
def endpoint(p):
    h=F(p['end_exact'])-F(p['start_exact'])
    x,v,a,j=(F(p[k]) for k in ('p','v','a','jerk'))
    return (x+h*(v+h*(a/2+h*j/6)),v+h*(a+h*j/2),a+h*j)
def text(v): return list(map(str,v))
def run():
    manifest=NATIVE/'artifact-sha256.json'; source=NATIVE/'reference-schedules.json'
    assert sha(manifest)=='aaae586029babf2e9381d09ff34fb7b488495630c48abde27ab9b4d8ece1a803'
    files=json.loads(manifest.read_text())['files']
    assert all(sha(NATIVE/k)==v for k,v in files.items())
    before={str(p):sha(p) for p in (source,manifest,BIND/'exact-reserve.json',BIND/'exact_reserve.py')}
    schedules=json.loads(source.read_text())['schedules']
    declared=json.loads((BIND/'exact-reserve.json').read_text())
    assert declared['source_schedule_sha256']==sha(source)
    checked=[]
    for s in schedules:
        if s['method'] not in ('ruckig','ruckig_min_08'): continue
        d=next(x for x in declared['cases'] if (x['case'],x['method'])==(s['case'],s['method']))
        ps=s['pieces']; total=F(0); nonzero=0; max_jump=F(0)
        assert len(ps)==len(d['pieces'])==d['piece_count']
        assert len(d['joins'])==len(ps)-1==d['join_count']
        assert F(ps[0]['start_exact'])==0
        assert tuple(F(ps[0][k]) for k in ('p','v','a'))==(0,0,0)
        for k,p in enumerate(ps):
            a,b=F(p['start_exact']),F(p['end_exact']); h=b-a
            coeff=tuple(F(p[n]) for n in ('p','v','a','jerk'))
            row=d['pieces'][k]
            assert h>0 and F(p['snap'])==0 and abs(coeff[3])<=F(15,2)
            assert row['index']==k and F(row['start'])==a and F(row['end'])==b
            assert F(row['duration'])==h and row['coefficients_p_v_a_j']==text(coeff)
            assert row['origin']==p['origin']
            if k:
                assert F(ps[k-1]['end_exact'])==a
                old=endpoint(ps[k-1]); delta=tuple(u-v for u,v in zip(coeff[:3],old))
                z=matrix(delta); rho=max(map(abs,z)); total+=rho
                nonzero+=int(rho>0); max_jump=max(max_jump,rho)
                j=d['joins'][k-1]
                assert j['left_piece']==k-1 and j['right_piece']==k and F(j['time'])==a
                assert j['left_endpoint']==text(old) and j['right_endpoint']==text(coeff[:3])
                assert j['delta_q_v_a']==text(delta) and j['transformed_delta']==text(z)
                assert F(j['exact_radius'])==rho<=F(1,10**15) and j['uniform_radius_check'] is True
        assert F(ps[-1]['end_exact'])==F(s['horizon_exact'])==F(d['horizon'])
        assert F(d['exact_sum_jump_radius'])==total
        reserve=(len(ps)-1)*F(1,10**15)
        assert F(d['uniform_sum_jump_radius'])==reserve>=total
        assert F(d['conditional_position_radius'])==F(41,320000)+reserve<F(1,5000)
        checked.append({'case':s['case'],'method':s['method'],'pieces':len(ps),
            'joins':len(ps)-1,'nonzero_joins':nonzero,'largest_join_m':str(max_jump),
            'exact_total_m':str(total),'uniform_total_m':str(reserve)})
    assert len(checked)==12 and sum(x['pieces'] for x in checked)==886
    assert F(1,100)+F(15,2)/480==200*F(41,320000)
    # Negative witnesses: checking position only cannot supply the needed radius.
    adversaries=[]
    for name,delta in [('velocity_only',(F(0),F(1),F(0))),('acceleration_only',(F(0),F(0),F(1))),('reinforcing_components',(F(1,1000),F(1,25),F(8,5)))]:
        z=matrix(delta)
        adversaries.append({'name':name,'reference_jump':text(delta),'transformed_jump':text(z),
            'radius':str(max(map(abs,z))),'position_only_radius':str(abs(delta[0])),
            'position_only_bound_fails':max(map(abs,z))>abs(delta[0])})
    assert all(x['position_only_bound_fails'] for x in adversaries)
    literal_file=BIND/'NativeData.lean'
    literals=literal_file.read_text(); literal_rows=[]
    for s in schedules:
        if s['method'] not in ('ruckig','ruckig_min_08'): continue
        name=s['case']+'__'+s['method']
        block=literals.split('def '+name+' : List Piece := [\n',1)[1].split('\n]',1)[0]
        rows=[line.strip().strip(',').strip('⟨⟩').split(',') for line in block.splitlines()]
        assert len(rows)==len(s['pieces'])
        for row,p in zip(rows,s['pieces']):
            actual=[F(x.strip('()')) for x in row]
            expected=[F(p[k]) for k in ('start_exact','end_exact','p','v','a','jerk')]
            assert actual==expected,(name,actual,expected)
        theorem=re.search(r'theorem '+re.escape(name)+r'_checked : check (\S+) '+re.escape(name)+r' = true := by decide \+kernel',literals)
        assert theorem and F(theorem[1].strip('()'))==F(s['horizon_exact'])
        literal_rows.append({'name':name,'pieces':len(rows),'horizon':s['horizon_exact']})
    before[str(literal_file)]=sha(literal_file)
    assert all(sha(Path(p))==h for p,h in before.items())
    out={'passed':True,'checked_utc':datetime.now(timezone.utc).isoformat(),'source_hashes':before,
        'native_builder_files_verified':len(files),'schedules':checked,'total_pieces':886,
        'total_joins':sum(x['joins'] for x in checked),'adversarial_witnesses':adversaries,
        'direct_lean_literal_binding':literal_rows,
        'scope':'Exact rational polynomial interpretation; no actual plant existence or task-goal proof.'}
    (HERE/'binding-audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('schedules','adversarial_witnesses')},indent=2))
if __name__=='__main__':run()
