from pathlib import Path
import hashlib,json,subprocess,datetime
from pypdf import PdfReader
p=Path(__file__).resolve().parent/'sources';rev='1581d4cbdd69a0faf34b2089614fe2a814316a6a'
paths={'sidorenko.pdf':'preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf','matching-entropy.pdf':'preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/main.pdf','maxcut.pdf':'preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf'}
rows=[]
for name,path in paths.items():
 url=f'https://raw.githubusercontent.com/openai/math/{rev}/{path}';f=p/name
 subprocess.run(['curl','-fL','--silent','--show-error',url,'-o',str(f)],check=True)
 pdf=PdfReader(f); f.with_suffix('.txt').write_text('\n'.join(f'\n=== PDF PAGE {i+1} ===\n'+(page.extract_text() or '') for i,page in enumerate(pdf.pages)))
 rows.append({'name':name,'path':path,'url':url,'pages':len(pdf.pages),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'text_sha256':hashlib.sha256(f.with_suffix('.txt').read_bytes()).hexdigest()})
 print(name,len(pdf.pages),flush=True)
(p/'source-manifest.json').write_text(json.dumps({'revision':rev,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2)+'\n')
