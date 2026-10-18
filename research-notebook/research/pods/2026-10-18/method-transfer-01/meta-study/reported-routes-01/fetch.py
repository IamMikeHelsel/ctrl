from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess,json,hashlib,urllib.parse,datetime
from pypdf import PdfReader
p=Path(__file__).resolve().parent
root=p.parents[1]
rev='1581d4cbdd69a0faf34b2089614fe2a814316a6a'
tree=json.loads((root/'corpus/reasoning_traces-tree.json').read_text())['tree']
items=[x for x in tree if x['path'].endswith('.pdf')]
def fetch(item):
 name=item['path'];url=f'https://raw.githubusercontent.com/openai/math/{rev}/reasoning_traces/'+urllib.parse.quote(name)
 data=(p/name).read_bytes() if (p/name).exists() else subprocess.check_output(['curl','--fail','--silent','--show-error','--max-time','40',url],timeout=45)
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==item['sha']
 dest=p/name;dest.write_bytes(data)
 reader=PdfReader(dest); pages=len(reader.pages);texts=[page.extract_text() for page in reader.pages]
 out=dest.with_suffix('.txt');out.write_text('\n\n'.join(f'PAGE {i+1}\n'+t for i,t in enumerate(texts)))
 dest.with_suffix('.pages.json').write_text(json.dumps(texts,indent=2)+'\n')
 return dict(file=name,url=url,git_blob_sha1=item['sha'],sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),pages=int(pages),text_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),text_words=len(out.read_text().split()),reading='downloaded, not yet fully read')
with ThreadPoolExecutor(max_workers=4) as ex:rows=list(ex.map(fetch,items))
(p/'source-manifest.json').write_text(json.dumps(dict(revision=rev,fetched_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sources=rows),indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['file','pages','text_words']} for r in rows],indent=2))
