#!/usr/bin/env python3
"""Independent frozen-source rebuild; no imports from builder Python helpers."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[4]
BUILDER = HERE.parent / 'builder-01'
BASE = WORK / 'lean-controls'
BUILD = HERE / 'build'
LOGS = HERE / 'logs'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    started = time.time()
    report = {'passed': False, 'steps': [], 'started_unix': started}
    def save(): (HERE/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    assert digest(BUILDER/'artifact-sha256.json') == '961ef23c1e27b446e1a6165079c4305f168fcaf23a40504528c374d5734f636e'
    assert digest(BUILDER/'source-freeze.json') == '29f21adf979b66c9b3ef06be14d1ff4865642d33c9b307bbdb70ac7ae7628be5'
    artifacts = json.loads((BUILDER/'artifact-sha256.json').read_text())
    for rel, expected in artifacts.items(): assert digest(BUILDER/rel) == expected, rel
    frozen = json.loads((BUILDER/'source-freeze.json').read_text())['files']
    for rel, meta in frozen.items(): assert digest(WORK/rel) == meta['sha256'], rel
    report['frozen_artifacts_checked'] = len(artifacts)
    report['frozen_source_files_checked'] = len(frozen)
    paths = {}
    for rel in frozen:
        p = WORK / rel
        if p.suffix != '.lean': continue
        m = '.'.join(p.relative_to(BASE).with_suffix('').parts) if p.is_relative_to(BASE) else p.stem
        assert m not in paths
        paths[m] = p
    ordered = []
    pending = set()
    def visit(m):
        if m in ordered: return
        assert m not in pending, m
        pending.add(m)
        for dep in re.findall(r'^(?:public\s+)?import\s+(\S+)', paths[m].read_text(), re.M):
            if dep.startswith('Mathlib.'): continue
            assert dep in paths, ('unfrozen local import', m, dep)
            visit(dep)
        pending.remove(m)
        ordered.append(m)
    for m in ['DirectSettling', 'MutationWitness']: visit(m)
    assert set(ordered) == set(paths), set(paths)-set(ordered)
    report['module_order'] = ordered
    report['source_sha256'] = {m: digest(paths[m]) for m in ordered}
    report['source_path'] = {m: str(paths[m].relative_to(WORK)) for m in ordered}
    env = os.environ.copy()
    env['ELAN_HOME'] = str(WORK/'.tools/elan')
    lake = str(WORK/'.tools/elan/bin/lake')
    def query(*a): return subprocess.check_output([lake, 'env', *a], cwd=BASE, env=env, text=True).strip()
    lean = query('which', 'lean')
    checker = str(Path(lean).with_name('leanchecker'))
    dependency_paths = [Path(s) if Path(s).is_absolute() else (BASE/s).resolve() for s in query('printenv', 'LEAN_PATH').split(':') if s]
    # The project's own old build directory must not resolve any local source.
    dependency_paths = [p for p in dependency_paths if not str(p).startswith(str(BASE/'.lake/build'))]
    env['LEAN_PATH'] = ':'.join([str(BUILD)]+list(map(str,dependency_paths)))
    env['PATH'] = str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    report['toolchain'] = subprocess.check_output([lean, '--version'], text=True, env=env).strip()
    report['lean_toolchain_file'] = (BASE/'lean-toolchain').read_text().strip()
    report['mathlib_revision'] = subprocess.check_output(['git','rev-parse','HEAD'], cwd=BASE/'.lake/packages/mathlib',text=True).strip()
    report['mathlib_status'] = subprocess.check_output(['git','status','--porcelain'], cwd=BASE/'.lake/packages/mathlib',text=True)
    report['lake_manifest_sha256'] = digest(BASE/'lake-manifest.json')
    report['lean_path'] = env['LEAN_PATH']
    def run(label,args,negative=False):
        path=LOGS/(label+'.log'); began=time.monotonic()
        with path.open('w') as out: p=subprocess.run(args,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=360)
        ok=(p.returncode!=0) if negative else (p.returncode==0)
        report['steps'].append({'label':label,'exit_code':p.returncode,'expected':'rejection' if negative else 'success','passed':ok,'seconds':time.monotonic()-began,'sha256':digest(path)})
        save(); print(label,p.returncode,flush=True)
        assert ok,label
        return path.read_text()
    public=[]
    for m in ordered:
        p=paths[m]
        code=re.sub(r'/-.*?-/|--[^\n]*','',p.read_text(),flags=re.S)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',code), m
        namespaces=re.findall(r'^namespace\s+(\S+)',code,re.M)
        assert len(namespaces)==1,(m,namespaces)
        for prefix,n in re.findall(r'^\s*([^\n]*?)\b(?:theorem|lemma)\s+([^\s{(:]+)',code,re.M):
            if not re.search(r'\bprivate\b',prefix): public.append(namespaces[0]+'.'+n)
        target=BUILD/(m.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True)
        assert not target.with_suffix('.olean').exists(), ('not fresh',target)
        shutil.copy2(p,target)
        run('build-'+m,[lean,'--root='+str(BUILD),'-o',str(target.with_suffix('.olean')),str(target)])
    assert len(public)==len(set(public))
    report['public_statements']=public
    audit=BUILD/'Audit.lean'
    audit.write_text('import DirectSettling\nimport MutationWitness\n'+'\n'.join('#print axioms '+n for n in public)+'\n')
    raw=run('axioms',[lean,str(audit)])
    axioms={n:[x.strip() for x in xs.split(',') if x.strip()] for n,xs in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",raw)}
    assert set(axioms)==set(public),(set(public)-set(axioms))
    assert all(set(v)<=ALLOWED for v in axioms.values())
    report['axioms']=axioms
    for m in ['ComparisonEnvelope','RobustHold','ScaledTracking','DirectReference','Settling','SettlingFixtures','DirectSettling','MutationWitness']:
        run('kernel-'+m,[checker,m,'-v'])
    for filename in ['ReviewWitnesses.lean']:
        source=HERE/filename
        if source.exists():
            target=BUILD/filename;shutil.copy2(source,target)
            run('review-'+source.stem,[lean,'--root='+str(BUILD),'-o',str(target.with_suffix('.olean')),str(target)])
            run('kernel-'+source.stem,[checker,source.stem,'-v'])
    for source in sorted((HERE/'negative').glob('*.lean')):
        target=BUILD/source.name;shutil.copy2(source,target)
        raw=run('negative-'+source.stem,[lean,str(target)],negative=True)
        assert ('unsolved goals' in raw or 'linarith failed' in raw),source
        assert not any(w in raw.lower() for w in ['unknown identifier','unknown module','timeout','maximum recursion','maximum number of heartbeats']),source
    report['source_unchanged']=all(digest(paths[m])==report['source_sha256'][m] for m in ordered)
    report['builder_artifacts_unchanged']=all(digest(BUILDER/p)==s for p,s in artifacts.items())
    report['passed']=report['source_unchanged'] and report['builder_artifacts_unchanged']
    report['seconds']=time.time()-started
    report['fresh_modules']=len(ordered)
    report['public_statement_count']=len(public)
    save();print(json.dumps({k:report[k] for k in ['passed','fresh_modules','public_statement_count','seconds']}),flush=True)

if __name__=='__main__': main()
