"""Independent copied-source replay of the saving lemma and semantic controls."""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-controls').is_dir())
RUN=HERE.parents[1]
SOURCE=RUN/'erdos/saving-replay-03'
BIN=ROOT/'.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin'
FRESH=HERE/'fresh-02'
assert not FRESH.exists(),'Preserve earlier attempts; do not overwrite a replay.'
FRESH.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mods=['Erdos128.WeightedGraph','Erdos128.CubicNeighborhood','Erdos128.OneStepSaving','MeaningfulControls']
pins={}; names=[]
for mod in mods:
    rel=Path(mod.replace('.','/')+'.lean')
    src=SOURCE/('original/'+str(rel) if mod!='MeaningfulControls' else str(rel))
    raw=src.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|#eval|run_cmd|\binitialize\b',raw)
    dest=FRESH/rel;dest.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(src,dest)
    pins[str(src.relative_to(ROOT))]=sha(src)
    ns='SavingReplayControls' if mod=='MeaningfulControls' else 'Erdos128'
    names.extend(ns+'.'+n for n in re.findall(r'^(?:@\[simp\]\s+)?theorem\s+(\w+)',raw,re.M))
audit='import MeaningfulControls\n'
audit+='\n'.join('#print axioms '+n for n in names)+'\n'
audit+='set_option pp.universes true\n#check @Erdos128.exists_oneStepSaving\n'
for n in ['RatProbabilityWeight','IsUnitProfile','weightedMean','weightedObjective','edgeMass','savingLQ']:
    audit+='#print Erdos128.'+n+'\n'
(FRESH/'Audit.lean').write_text(audit)
packages=ROOT/'lean-controls/.lake/packages'
libs=sorted(p/'.lake/build/lib/lean' for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir())
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[FRESH,*libs]))
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_sha256':pins,'lean_sha256':sha(BIN/'lean'),'checker_sha256':sha(BIN/'leanchecker'),
 'executed_version':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),
 'executed_mathlib_pin':json.loads((ROOT/'lean-controls/lake-manifest.json').read_text()),
 'upstream_environment':(SOURCE/'original/lean-toolchain').read_text().strip(),
 'scope':'Unchanged source in existing Lean4.35 environment; package caches imported; no graph endpoint.',
 'lean_path':env['LEAN_PATH'],'steps':[],'passed':False}
def save():(HERE/'verification-02.json').write_text(json.dumps(record,indent=2)+'\n')
def run(label,args):
    start=time.monotonic()
    r=subprocess.run(list(map(str,args)),cwd=FRESH,env=env,capture_output=True,text=True,timeout=240)
    out=r.stdout+r.stderr;(HERE/('attempt02-'+label+'.log')).write_text(out)
    record['steps'].append({'label':label,'command':list(map(str,args)),'exit_code':r.returncode,'seconds':time.monotonic()-start,'log_sha256':sha(HERE/('attempt02-'+label+'.log'))})
    save();print(label,r.returncode,flush=True)
    assert r.returncode==0,out
    return out
for mod in mods+['Audit']:
    rel=Path(mod.replace('.','/')+'.lean')
    out=run('build-'+mod,[BIN/'lean','-DmaxHeartbeats=3000000','-DmaxRecDepth=4000','-o',rel.with_suffix('.olean'),rel])
    if mod=='Audit':
        ax={n:[a.strip() for a in body.split(',') if a.strip()] for n,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
        assert set(ax)==set(names),(set(ax),set(names))
        assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in ax.values())
        record['axioms']=ax;save()
for mod in mods+['Audit']:run('kernel-'+mod,[BIN/'leanchecker',mod,'-v'])
assert all(sha(ROOT/name)==value for name,value in pins.items())
record['passed']=True;record['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print(json.dumps({'passed':True,'audited_declarations':len(names),'steps':len(record['steps'])}),flush=True)
