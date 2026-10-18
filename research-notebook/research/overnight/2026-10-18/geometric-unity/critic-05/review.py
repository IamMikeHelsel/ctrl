from pathlib import Path
import hashlib, json, os, re, subprocess, time
B=Path(__file__).resolve().parent
R=B.parents[4]
S=B.parent/'builder-05'
P=R/'lean-controls'
CACHE=B/'cache'/'review-01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
BUILDER='922cb7a3c80a174c15363ab3120701c95364944dcea696f7e999a59ee26a8a2f'
ledger=json.loads((S/'source-ledger.json').read_text())

def verify_all():
    result={}
    pins=dict(ledger['prior_manifest_pins'])
    pins[str(S.relative_to(R))]=BUILDER
    for rel,pin in pins.items():
        d=R/rel
        manifest=d/'SHA256SUMS'
        assert sha(manifest)==pin, (rel,'manifest')
        lines=manifest.read_text().splitlines()
        for line in lines:
            h,f=line.split('  ',1)
            assert sha(d/f)==h,(rel,f)
        result[rel]={'manifest_sha256':pin,'entries_checked':len(lines)}
    for mod,rec in ledger['inherited'].items():
        assert sha(S/(mod+'.lean'))==rec['sha256']==sha(S/rec['origin'])
    return result
before=verify_all()
(B/'preservation-before.json').write_text(json.dumps(before,indent=2)+'\n')
modules={p.stem:p for p in S.glob('*.lean')}
assert len(modules)==25
order=[];visiting=set()
def visit(mod):
    if mod in order:return
    assert mod not in visiting
    visiting.add(mod)
    for name in re.findall(r'^import\s+(\S+)',modules[mod].read_text(),re.M):
        if name in modules:visit(name)
    visiting.remove(mod);order.append(mod)
for mod in sorted(modules):visit(mod)
assert set(order)==set(modules)
assert not CACHE.exists(), 'preserve earlier attempts'
CACHE.mkdir(parents=True)
env=os.environ.copy();env['ELAN_HOME']=str(R/'.tools/elan')
lake=R/'.tools/elan/bin/lake'
lean=Path(subprocess.check_output([str(lake),'env','which','lean'],cwd=P,env=env,text=True).strip())
version=subprocess.check_output([str(lean),'--version'],text=True).strip()
assert '4.35.0' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
pin=next(p for p in json.loads((P/'lake-manifest.json').read_text())['packages'] if p['name']=='mathlib')['rev']
assert pin=='56a005855ea17e0b0958f73ec801ae140b0a1679'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P/'.lake/packages/mathlib',text=True).strip()==pin
assert not subprocess.check_output(['git','status','--porcelain'],cwd=P/'.lake/packages/mathlib',text=True).strip()
paths=subprocess.check_output([str(lake),'env','printenv','LEAN_PATH'],cwd=P,env=env,text=True).strip().split(':')
deps=[]
for p in paths:
    path=(P/p).resolve()
    if path==(P/'.lake/build/lib/lean').resolve():continue
    assert '/.lake/packages/' in str(path) or path==lean.parent.parent/'lib/lean',path
    deps.append(str(path))
env['LEAN_PATH']=':'.join([str(CACHE)]+deps)
env['PATH']=str(lean.parent)+':'+env['PATH']
config={'compiler':str(lean),'version':version,'mathlib_rev':pin,'module_order':order,'LEAN_PATH':env['LEAN_PATH'],'ELAN_HOME':env['ELAN_HOME'],'PATH':env['PATH'],'local_sources_fresh':True,'builder_cache_used':False,'root_project_cache_used':False}
(B/'environment.json').write_text(json.dumps(config,indent=2)+'\n')
steps=[]
def run(name,cmd):
    start=time.monotonic()
    p=subprocess.run(cmd,cwd=CACHE,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    (B/'logs'/(name+'.txt')).write_text(p.stdout)
    steps.append({'name':name,'returncode':p.returncode,'seconds':time.monotonic()-start,'command':cmd})
    (B/'progress.json').write_text(json.dumps(steps,indent=2)+'\n')
    print(name,p.returncode,flush=True)
    assert p.returncode==0,p.stdout
for mod in order:
    raw=modules[mod].read_bytes()
    assert not re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide)\b',raw),mod
    (B/'source'/(mod+'.lean')).write_bytes(raw)
    (CACHE/(mod+'.lean')).write_bytes(raw)
    run('fresh-'+mod,[str(lean),'--root='+str(CACHE),'-o',str(CACHE/(mod+'.olean')),str(CACHE/(mod+'.lean'))])
for mod in order:run('kernel-'+mod,[str(lean.with_name('leanchecker')),mod,'-v'])
assert verify_all()==before
(B/'fresh-result.json').write_text(json.dumps({'status':'PASS','modules':len(order),'kernel_replays':len(order),'steps':steps,'preservation':before},indent=2)+'\n')
