"""Small exact-rational client. JSON parsing is outside the Lean theorem.
The generated decision and its consequence are compiled and kernel checked.
Run verify.py first. Output folders must be new; evidence is never overwritten.
"""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,os,re,subprocess
import dev
HERE=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def keys(v,want):
    if not isinstance(v,dict) or set(v)!=set(want): raise ValueError('wrong fields: '+str(want))
def rat(v):
    if not isinstance(v,str) or len(v)>128 or not re.fullmatch(r'-?[0-9]+(?:/[0-9]+)?',v):
        raise ValueError('rationals must be integer or numerator/denominator strings')
    q=Fraction(v)
    return f'({q.numerator}/{q.denominator}:ℚ)'
def version(v):
    if type(v)!=int or v<0: raise ValueError('version must be a nonnegative integer')
    return str(v)
def base(b):
    keys(b,['events','offset','width','version'])
    if not isinstance(b['events'],list): raise ValueError('events must be a list')
    ev=[]
    for e in b['events']:
        if not isinstance(e,list) or len(e)!=2: raise ValueError('an event has time and increment')
        ev.append('('+rat(e[0])+','+rat(e[1])+')')
    return '⟨['+','.join(ev)+'],'+rat(b['offset'])+','+rat(b['width'])+','+version(b['version'])+'⟩'
def task(t):
    fields=['goal','request','deadline','speed','accel','jerkLimit','version'];keys(t,fields)
    return '⟨'+','.join([rat(t[k]) for k in fields[:-1]]+[version(t['version'])])+'⟩'
def timing(t):
    fields=['completion','commitTime','dispatch'];keys(t,fields)
    return '⟨'+','.join(rat(t[k]) for k in fields)+'⟩'
def pending(p):
    keys(p,['base','task','execution','delta','candidates'])
    if not isinstance(p['candidates'],list): raise ValueError('candidates must be a list')
    return '⟨'+','.join([base(p['base']),task(p['task']),rat(p['execution']),rat(p['delta']),
        '['+','.join(rat(x) for x in p['candidates'])+']'])+'⟩'

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('output',type=Path)
    args=ap.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    for name,item in json.loads((HERE/'client-freeze.json').read_text())['files'].items():
        assert sha(HERE/name)==item['sha256'],name
    v=json.loads(args.input.read_text());keys(v,['pending','liveBase','liveTask','timing'])
    text='import FutureCommit\nnamespace ExactClient\nopen RobotMotion RobotMotion.FutureCommit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    text+='def p : Pending := '+pending(v['pending'])+'\n'
    text+='def b : Base := '+base(v['liveBase'])+'\n'
    text+='def t : Task := '+task(v['liveTask'])+'\n'
    text+='def tm : Timing := '+timing(v['timing'])+'\n'
    env,lean,deps=dev.environment();fresh=HERE/'.cache/fresh'
    metadata=json.loads((HERE/'verification.json').read_text());assert metadata['status']=='PASS'
    freeze=json.loads((HERE/'source-freeze.json').read_text())
    assert sha(HERE/'source-freeze.json')==metadata['source_freeze_sha256']
    for name,item in freeze['files'].items(): assert sha(HERE/name)==item['sha256'],name
    bindings=json.loads((HERE/'input-bindings.json').read_text())
    for item in bindings['sources'].values(): assert sha(dev.WORK/item['path'])==item['sha256']
    for group in ['closure_manifests','toolchain_files']:
        for name,digest in bindings[group].items(): assert sha(dev.WORK/name)==digest
    assert sha(Path(lean))==metadata['lean_sha256']
    for name,item in json.loads((HERE/'compiled-object-hashes.json').read_text()).items():
        assert sha(fresh/name)==item['sha256'],name
    deps=':'.join(p for p in deps.split(':') if Path(p).resolve()!=(dev.BASE/'.lake/build/lib/lean').resolve())
    env['LEAN_PATH']=':'.join([str(out),str(fresh),deps])
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    def run(argv,name):
        r=subprocess.run(argv,cwd=out,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/(name+'.log')).write_text(r.stdout)
        if r.returncode: raise RuntimeError(name+' failed; see saved log')
        return r.stdout
    probe=out/'ClientProbe.lean';probe.write_text(text+'#eval commitOK p b t tm\nend ExactClient\n')
    observed=run([lean,'--root='+str(out),str(probe)],'probe').strip()
    assert observed in ['true','false'],observed
    theorem='theorem decision : commitOK p b t tm = '+observed+' := by decide +kernel\n'
    if observed=='true':
        theorem+='noncomputable theorem reference_contract : ReferenceContract b t (commit p b t tm) p.execution := (successful_commit_contract decision).2.2.2.2.2\n'
    else:
        theorem+='theorem retained_live : commit p b t tm = b := rejected_retains_live decision\n'
    proof=out/'ClientProof.lean';proof.write_text(text+theorem+'#print axioms decision\nend ExactClient\n')
    run([lean,'--root='+str(out),'-o',str(proof.with_suffix('.olean')),str(proof)],'proof')
    run([str(Path(lean).parent/'leanchecker'),'ClientProof','-v'],'kernel')
    result={'decision':observed=='true','input_sha256':sha(args.input),'source_sha256':sha(proof),
        'object_sha256':sha(proof.with_suffix('.olean')),'compiled_proof':True,'kernel_replay':True,
        'meaning':'reference contract for supplied live state and ideal clock' if observed=='true' else 'supplied live state retained; new task not certified',
        'boundary':'JSON parser, runtime clock and atomic state capture are not formally verified; no hardware or physical-state claim'}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__': main()
