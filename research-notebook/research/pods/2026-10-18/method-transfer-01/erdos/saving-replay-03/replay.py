#!/usr/bin/env python3
"""Fresh copied-source build and separate checker under the existing 4.35 pin.

Does not install, edit upstream sources, change pins, or reuse saving oleans.
Every invocation creates its own evidence/build directory and preserves errors.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lean-controls').is_dir())
SOURCE=HERE.parent/'comparison-02/upstream-source'
BIN=Path('/Users/mike/.elan/toolchains/leanprover--lean4---v4.35.0/bin')
PACKAGES=ROOT/'lean-controls/.lake/packages'
MODULES=['Erdos128.WeightedGraph','Erdos128.CubicNeighborhood','Erdos128.OneStepSaving']
ALLOWED={'propext','Classical.choice','Quot.sound'}

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    original=HERE/'original'
    for name in [*[(m.replace('.','/')+'.lean') for m in MODULES],
                 'lean-toolchain','lake-manifest.json','lakefile.toml']:
        dst=original/name;dst.parent.mkdir(parents=True,exist_ok=True)
        if dst.exists():assert dst.read_bytes()==(SOURCE/name).read_bytes()
        else:shutil.copyfile(SOURCE/name,dst)
    work=Path(tempfile.mkdtemp(prefix='unchanged-435-',dir=HERE))
    sources={}
    declarations=[]
    for mod in MODULES:
        rel=Path(mod.replace('.','/')).with_suffix('.lean')
        src=original/rel;dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(src,dst);sources[mod]={'original':str(src.relative_to(HERE)),
          'copied':str(dst.relative_to(HERE)),'sha256':sha(src)}
        declarations += ['Erdos128.'+name for name in re.findall(r'^theorem\s+([\w]+)',src.read_text(),re.M)]
        declarations += ['Erdos128.'+name for name in re.findall(r'^@\[simp\]\s+theorem\s+([\w]+)',src.read_text(),re.M)]
    audit='import Erdos128.OneStepSaving\nset_option format.width 120\n'
    audit+='\n'.join('#print axioms '+name for name in declarations)+'\n'
    audit+='set_option pp.universes true\n#check @Erdos128.exists_oneStepSaving\n#print Erdos128.RatProbabilityWeight\n'
    for name in ['IsUnitProfile','weightedMean','edgeMass','weightedObjective','centerRadiusQ','savingLQ']:
        audit+='#print Erdos128.'+name+'\n'
    (work/'Audit.lean').write_text(audit)
    deps=sorted(p/'.lake/build/lib/lean' for p in PACKAGES.iterdir() if (p/'.lake/build/lib/lean').is_dir())
    env=os.environ.copy();env['PATH']=str(BIN)+os.pathsep+env.get('PATH','')
    env['LEAN_PATH']=os.pathsep.join(map(str,[work,*deps]))
    manifest=json.loads((ROOT/'lean-controls/lake-manifest.json').read_text())
    result={'started_utc':datetime.now(timezone.utc).isoformat(),
      'kind':'Unchanged upstream source built in existing Lean4.35/mathlib environment; not a Lean4.30 replay',
      'work':str(work.relative_to(HERE)),'source':sources,'source_changes':False,
      'upstream_toolchain':(original/'lean-toolchain').read_text().strip(),
      'executed_lean':subprocess.check_output([str(BIN/'lean'),'--version'],text=True).strip(),
      'mathlib_pin':next(p for p in manifest['packages'] if p['name']=='mathlib'),
      'lean_path':env['LEAN_PATH'],'declarations_audited':declarations,'runs':[],'axioms':{}}
    def save():
        result['source_hashes_stable']=all(sha(HERE/v['original'])==v['sha256']==sha(HERE/v['copied']) for v in sources.values())
        (work/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    def run(label,cmd,limit=240):
        start=time.monotonic()
        try:
            proc=subprocess.run(cmd,cwd=work,env=env,text=True,capture_output=True,timeout=limit)
            output=proc.stdout+proc.stderr;code=proc.returncode
        except subprocess.TimeoutExpired as exc:
            output=str(exc.stdout or '')+'\n'+str(exc.stderr or '')+'\nTIMEOUT\n';code=124
        (work/(label+'.log')).write_text(output)
        result['runs'].append({'label':label,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'log':label+'.log'})
        save();print(label,code,flush=True)
        return code,output
    for mod in MODULES+['Audit']:
        rel=Path(mod.replace('.','/')).with_suffix('.lean')
        code,out=run('compile-'+mod.replace('.','-'),[str(BIN/'lean'),'-DmaxHeartbeats=3000000','-DmaxRecDepth=4000','-o',str(rel.with_suffix('.olean')),str(rel)])
        if code:
            result['passed']=False;result['stopped_at']='compile '+mod;save();return 1
        if mod=='Audit':
            result['axioms']={name:[a.strip() for a in axes.split(',') if a.strip()]
              for name,axes in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",out)}
            assert set(result['axioms'])==set(declarations),(result['axioms'].keys(),declarations)
            assert all(set(axes)<=ALLOWED for axes in result['axioms'].values())
    for mod in MODULES+['Audit']:
        code,_=run('kernel-'+mod.replace('.','-'),[str(BIN/'leanchecker'),mod,'-v'])
        if code:
            result['passed']=False;result['stopped_at']='kernel '+mod;save();return 1
    result['passed']=True;result['completed_utc']=datetime.now(timezone.utc).isoformat();save()
    print(json.dumps({'passed':True,'work':str(work),'audits':len(declarations)}),flush=True)
    return 0

if __name__=='__main__':sys.exit(main())
