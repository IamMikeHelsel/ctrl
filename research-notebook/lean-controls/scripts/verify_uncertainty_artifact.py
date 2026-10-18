#!/usr/bin/env python3
"""Derive and replay all12 rate/sector/remainder certificates from model data.

SymPy derivation is untrusted. Byte agreement binds it to the independently
proved UncertainLag.vertex_identity; each emitted proof is freshly checked.
Two mutation tests exercise distinct model-to-certificate boundary failures.
"""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time
import sympy as s
from generate_interval_certificate import produce, rational
from lean_runtime import runtime

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence/uncertainty-artifact'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(blob): return hashlib.sha256(blob).hexdigest()

def derive(data):
    P=s.Matrix([[rational(x) for x in row] for row in data['P']])
    K=s.Matrix([[rational(x) for x in data['positive_feedback_coefficients']]])
    lo,hi=map(rational,data['rate_interval'])
    h,r,alpha,theta,q=s.symbols('h r alpha theta q')
    F=s.Matrix([[1,h,theta*h*h],[0,1,h-theta*r*h*h],[0,0,1-r*h+theta*r*r*h*h]])
    g=s.Matrix([(s.Rational(1,2)-theta)*h*h,theta*r*h*h,r*h-theta*r*r*h*h])
    transition=F-g*alpha*K
    cases=[]
    for ai,av in enumerate(map(rational,data['sector_interval'])):
        for li,lv in enumerate(map(rational,data['remainder_interval'])):
            B=transition.subs({alpha:av,theta:lv,r:lo+(hi-lo)*q}).applyfunc(s.expand)
            power=[B.applyfunc(lambda z:s.Poly(z,q).nth(k)) for k in range(3)]
            coeff=[sum((power[k]*s.binomial(j,k)/s.binomial(2,k) for k in range(j+1)),s.zeros(3)) for j in range(3)]
            reconstructed=sum((s.binomial(2,j)*q**j*(1-q)**(2-j)*coeff[j] for j in range(3)),s.zeros(3))
            assert (reconstructed-B).applyfunc(s.expand)==s.zeros(3)
            for j,V in enumerate(coeff):
                name=f'UncertainA{ai}L{li}R{j}'
                case={'P':[[str(x) for x in row] for row in P.tolist()],
                      'A_coefficients':[[[str(s.Poly(V[i,k],h).nth(d)) for k in range(3)] for i in range(3)] for d in range(3)],
                      'decay_margin':data['decay_margin'],'partition':data['partition']}
                cases.append((name,case))
    assert len(cases)==12
    return cases

def audited_source(source):
    ns=re.search(r'^namespace (\S+)',source,re.M).group(1)
    names=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',source,re.M)]
    return source+'\n'+''.join('#print axioms '+n+'\n' for n in names),names

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    spec=ROOT/'benchmarks/uncertain-lag.json'
    source=ROOT/'LeanControls/UncertainLag.lean'
    before=digest(source.read_bytes())
    lake,env=runtime(ROOT)
    report={'started_utc':datetime.now(timezone.utc).isoformat(),'status':'running',
            'spec_sha256':digest(spec.read_bytes()),'bridge_sha256':before,
            'deriver_sha256':digest(Path(__file__).read_bytes()),'cases':[],'mutations':[],
            'scope':'Exact certificate regeneration, fresh Lean replay and negative model-binding tests; not physical validation or verified producer.'}
    def save(): (OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    save()
    try:
        cases=derive(json.loads(spec.read_text()))
        def check(item):
            name,data=item
            generated,witness=produce(data,name)
            installed=ROOT/f'LeanControls/Generated/{name}.lean'
            if generated.strip()!=installed.read_text().strip():
                raise RuntimeError(name+': regenerated proof differs from installed source')
            (OUT/(name+'.input.json')).write_text(json.dumps(data,indent=2)+'\n')
            (OUT/(name+'.certificate.json')).write_text(json.dumps(witness,indent=2)+'\n')
            blob,names=audited_source(generated)
            start=time.monotonic()
            with tempfile.TemporaryDirectory(prefix='uncertain-certificate-') as tmp:
                candidate=Path(tmp)/(name+'.lean');candidate.write_text(blob)
                run=subprocess.run([lake,'env','lean',str(candidate)],cwd=ROOT,env=env,capture_output=True,text=True,timeout=240)
            log=run.stdout+run.stderr;(OUT/(name+'.log')).write_text(log)
            records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
            axioms={n:sorted({a.strip() for a in ax.split(',') if a.strip()}) for n,ax in records}
            axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",log)})
            if run.returncode or set(axioms)!=set(names) or any(not set(ax)<=ALLOWED for ax in axioms.values()):
                raise RuntimeError(name+': proof or axiom audit failed')
            return {'name':name,'source_sha256':digest(installed.read_bytes()),
                    'regenerated_source_sha256':digest(generated.encode()),
                    'equality':'identical modulo terminal whitespace',
                    'seconds':time.monotonic()-start,'exit_code':run.returncode,'axioms':axioms}
        with ThreadPoolExecutor(max_workers=3) as pool:
            for result in pool.map(check,cases):
                report['cases'].append(result);save()
        original=source.read_text()
        old='2 • polynomialNominal 1 t z alpha theta - (1/2:ℝ) •\n      (polynomialNominal (9/10) t z alpha theta + polynomialNominal (11/10) t z alpha theta)'
        assert original.count(old)==1
        mid=original.replace(old,'polynomialNominal 1 t z alpha theta')
        old='r * (u-current 2)';assert original.count(old)==1
        wrong_rate=original.replace(old,'u-current 2')
        for label,blob,expected in [
            ('midpoint-is-not-Bernstein-coefficient',mid,'theorem vertex_identity'),
            ('dropping-actual-rate-changes-ODE',wrong_rate,'theorem heldSegment_ode')]:
            start=time.monotonic()
            with tempfile.TemporaryDirectory(prefix='uncertain-mutation-') as tmp:
                candidate=Path(tmp)/'UncertainLag.lean';candidate.write_text(blob)
                run=subprocess.run([lake,'env','lean',str(candidate)],cwd=ROOT,env=env,capture_output=True,text=True,timeout=240)
            log=run.stdout+run.stderr;(OUT/(label+'.log')).write_text(log)
            errors=re.findall(r'UncertainLag\.lean:(\d+):\d+: error:',log)
            lines=blob.splitlines();start_line=next(i+1 for i,line in enumerate(lines) if line.startswith(expected))
            end_line=next((i+1 for i in range(start_line,len(lines)) if lines[i].startswith(('theorem ','def ','/--'))),len(lines)+1)
            rejected_expected=any(start_line<=int(line)<end_line for line in errors)
            if run.returncode==0 or not rejected_expected:
                raise RuntimeError(label+': expected bridge rejection not observed')
            report['mutations'].append({'label':label,'exit_code':run.returncode,
                'expected_theorem':expected,'expected_failure_observed':rejected_expected,
                'error_lines':errors,'seconds':time.monotonic()-start,
                'not_a_theorem':'Rejection of a changed model paired with old proof, not physical unsafety.'})
            save()
        assert digest(source.read_bytes())==before
        report['status']='passed'
    except Exception as exc:
        report['status']='failed';report['error']=str(exc);raise
    finally:
        report['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print('All12 regenerated certificates and both model-boundary rejection checks passed.')

if __name__=='__main__': main()
