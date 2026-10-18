import pathlib, subprocess, hashlib, json, datetime
from html.parser import HTMLParser
root=pathlib.Path(__file__).parent
sources=[
('harvard-thesis-identity','https://legacy-www.math.harvard.edu/history/bott/bottbio/node6.html','html','Harvard Mathematics historical advisor student table; independent bibliographic identity'),
('official-home','https://geometricunity.org/','html','Author project homepage'),
('gu-2021','https://geometricunity.nyc3.digitaloceanspaces.com/Geometric_Unity-Draft-April-1st-2021.pdf','pdf','Author manuscript, working draft v1.0'),
('oxford-official','https://geometricunity.org/2013-oxford-lecture/','html','Author project transcript page; speech primary, transcription editorial'),
('oxford-2020-supplement','https://theportal.group/a-portal-special-presentation-geometric-unity-a-first-look/','html','Community transcript of author 2013 lecture and 2020 supplement'),
('ucsd-2025','https://theportal.group/from-dark-to-geometric-energy-a-sector-of-geometric-unity/','html','Community-hosted author lecture entry and partial transcript'),
('jaimungal-2025','https://theportal.group/curt-jaimungal-with-eric-weinstein-geometric-unity-40-years-in-the-making/','html','Community transcript of author interview'),
('keating-2021','https://theportal.group/into-the-impossible-eric-weinstein-geometric-unity-revealed/','html','Community transcript of author interview'),
('thesis-1992','https://theportal.wiki/images/4/4f/Eric_Dissertation_-_Extension_of_Self-Dual_Yang-Mills_equations_across_the_8th_dimension.pdf','pdf','Author dissertation scan, community mirror')]
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.skip=0;self.parts=[];self.links=[]
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['a','iframe','img']:
   d=dict(a);u=d.get('href') or d.get('src');
   if u:self.links.append(u)
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip and d.strip():self.parts.append(d.strip())
ledger=[]
for name,url,ext,kind in sources:
 p=root/f'{name}.{ext}'
 run=subprocess.run(['curl','-L','--fail','--max-time','60','--silent','--show-error',url,'-o',str(p)],capture_output=True,text=True)
 record=dict(id=name,url=url,kind=kind,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='downloaded' if run.returncode==0 else 'failed')
 if run.returncode==0:
  b=p.read_bytes();record.update(path=p.name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if ext=='html':
   ex=Extract();ex.feed(b.decode(errors='replace'));(root/f'{name}.txt').write_text('\n'.join(ex.parts));(root/f'{name}-links.json').write_text(json.dumps(ex.links,indent=2))
 else:record['error']=run.stderr
 ledger.append(record)
(root/'provenance.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps(ledger,indent=2))
