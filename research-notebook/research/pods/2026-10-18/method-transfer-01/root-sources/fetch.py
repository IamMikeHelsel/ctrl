"""Fetch a disclosed source sample at the corpus revision; never execute it."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess
import json
import hashlib
import urllib.parse

HERE = Path(__file__).resolve().parent
CORPUS = HERE.parent/'corpus'
sha = json.loads((CORPUS/'source-manifest.json').read_text())['revision']
selection = {
 '087-introduction.tex':'preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/build/sections/introduction.tex',
 '087-feasibility.tex':'preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/build/sections/feasibility.tex',
 '087-holomorphic-mass.tex':'preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/build/sections/holomorphic-mass.tex',
 '095-introduction.tex':'preprints/Hyperbolicity-Cones-Without-Semidefinite-Lifts-October-5-2026/build/source/01-introduction.tex',
 '095-obstruction.tex':'preprints/Hyperbolicity-Cones-Without-Semidefinite-Lifts-October-5-2026/build/source/05-obstruction.tex',
 '095-lift-introduction.tex':'preprints/An-Exact-Semidefinite-Lift-of-a-Nonspectrahedral-Hyperbolicity-Cone-October-5-2026/build/sections/introduction.tex',
 '282-introduction.tex':'preprints/Scale-and-conformal-symmetry-in-four-dimensional-operational-quantum-field-theory-September-26-2026/build/sections/01-introduction.tex',
 '282-foundations.tex':'preprints/Scale-and-conformal-symmetry-in-four-dimensional-operational-quantum-field-theory-September-26-2026/build/sections/02-foundations.tex',
 '087-reasoning.pdf':'reasoning_traces/symmetric-and-general-mahler-conjectures.pdf',
}
def fetch(pair):
 name,path=pair
 url='https://raw.githubusercontent.com/openai/math/'+sha+'/'+urllib.parse.quote(path,safe='/')
 data=subprocess.check_output(['curl','--fail','--silent','--show-error','--max-time','40',url])
 (HERE/name).write_bytes(data)
 return {'file':name,'source_path':path,'url':url,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'read_status':'downloaded; see root reading record for depth'}
with ThreadPoolExecutor(max_workers=4) as ex:
 rows=list(ex.map(fetch,selection.items()))
(HERE/'source-manifest.json').write_text(json.dumps({'revision':sha,'sources':rows},indent=2)+'\n')
print(json.dumps({'downloaded':len(rows),'bytes':sum(r['bytes'] for r in rows)}))
