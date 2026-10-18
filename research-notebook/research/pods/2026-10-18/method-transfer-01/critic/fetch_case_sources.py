from pathlib import Path
import subprocess,json,hashlib,concurrent.futures,datetime
P=Path(__file__).resolve().parent/'sources';REV='1581d4cbdd69a0faf34b2089614fe2a814316a6a'
CASES={'102':'The-Unique-Games-Theorem-September-23-2026','159':'Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026','197':'A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026','221':'The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026'}
def curl(u,p):subprocess.run(['curl','-fsSL',u,'-o',str(p)],check=True)
def fetch(item):
 n,folder=item;out=P/n;out.mkdir(exist_ok=True);url=f'https://api.github.com/repos/openai/math/contents/preprints/{folder}?ref={REV}';curl(url,out/'directory.json');d=json.loads((out/'directory.json').read_text());files={}
 for x in d:
  if x['name'].endswith(('.tex','.md')):
   u=f'https://raw.githubusercontent.com/openai/math/{REV}/'+x['path'];p=out/x['name'];curl(u,p);files[x['path']]={'url':u,'local':str(p.relative_to(P)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
 path='lean/docs/'+n+'.md';u=f'https://raw.githubusercontent.com/openai/math/{REV}/'+path;p=out/'formalization.md';curl(u,p);files[path]={'url':u,'local':str(p.relative_to(P)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
 print(n,list(files),flush=True);return n,files
res=dict(concurrent.futures.ThreadPoolExecutor(max_workers=4).map(fetch,CASES.items()))
(P/'case-source-manifest.json').write_text(json.dumps({'revision':REV,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cases':res},indent=2)+'\n')
