from pathlib import Path
from urllib.request import Request,urlopen
from datetime import datetime,timezone
import hashlib,json
B=Path(__file__).resolve().parent
urls={
'author-draft.pdf':'https://geometricunity.nyc3.digitaloceanspaces.com/Geometric_Unity-Draft-April-1st-2021.pdf',
'official-home.html':'https://geometricunity.org/',
'author-home.html':'https://ericweinstein.org/',
'spin-roadmap.md':'https://raw.githubusercontent.com/TauCetiProject/TauCetiRoadmap/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md',
'keating-author-lecture.html':'https://theportal.group/from-dark-to-geometric-energy-a-sector-of-geometric-unity/',
'jaimungal-author-conversation.html':'https://theportal.group/curt-jaimungal-with-eric-weinstein-geometric-unity-40-years-in-the-making/',
'prior-audit.pdf':'https://kleis.io/docs/papers/geometric_unity_audit.pdf',
}
rows=[]
for name,url in urls.items():
 row={'name':name,'url':url,'retrieved_utc':datetime.now(timezone.utc).isoformat()}
 try:
  with urlopen(Request(url,headers={'User-Agent':'ResearchNotebook/1.0'}),timeout=25) as r:
   b=r.read();row.update(final_url=r.url,status=r.status)
  (B/'sources'/name).write_bytes(b)
  row.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e: row['error']=str(e)
 rows.append(row)
(B/'source-refresh.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
