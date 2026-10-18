import subprocess,json,pathlib,concurrent.futures,hashlib
base=pathlib.Path(__file__).parent
small=['yutk/gu','stubbornjello-oss/gu','justindbilyeu/geometric-unity-gate1','ResponseGU/Response_to_Geometric_Unity','disruptionjoe/gu-source-action']
repos=small+['disruptionjoe/gu-formalization','Dizzident/GeometricUnity','disruptionjoe/dynamic-unity']
work=[]
for repo in repos:
 key=repo.replace('/','--');commit=json.loads((base/'metadata'/f'{key}-commit.json').read_text())['sha'];tree=json.loads((base/'metadata'/f'{key}-tree.json').read_text())['tree']
 for x in tree:
  p=x['path']; select=repo in small or p in ['README.md','LICENSE-CODE.md','LICENSE-DOCS.md','REPRODUCE.md','lean-toolchain','lakefile.lean','lake-manifest.json']
  if repo=='disruptionjoe/gu-formalization': select |= p.startswith('Lean/') and p.endswith('.lean')
  if repo=='Dizzident/GeometricUnity': select |= (('Shiab' in p or 'Clifford' in p) and p.startswith(('src/','tests/'))) or p in ['src/Gu.ReferenceCpu/EinsteinianShiab4D.cs']
  if x['type']=='blob' and select and pathlib.PurePosixPath(p).name not in ['AGENTS.md','Agents Start Here.md']:
   work.append((repo,commit,x))
def get(t):
 repo,commit,x=t;p=x['path'];out=base/'sources'/repo.replace('/','--')/p;out.parent.mkdir(parents=True,exist_ok=True);url=f'https://raw.githubusercontent.com/{repo}/{commit}/{p}';subprocess.run(['curl','-fLsS',url,'-o',str(out)],check=True)
 b=out.read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==x['sha'],p
 return dict(repo=repo,commit=commit,path=p,url=url,bytes=len(b),git_blob_sha1=blob,sha256=hashlib.sha256(b).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex: result=list(ex.map(get,work))
(base/'DOWNLOAD-MANIFEST.json').write_text(json.dumps({'retrieved':'2026-10-18','mode':'source-only; no repository code executed; selected files for large repositories','files':result},indent=2)+'\n')
print(len(result),'files',sum(x['bytes'] for x in result),'bytes')
