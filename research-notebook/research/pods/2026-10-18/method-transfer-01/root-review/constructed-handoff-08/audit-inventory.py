from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parent
B=R.parents[1]/'controls/constructed-handoff-08'
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   e=s.find('\n',i);i=len(s) if e<0 else e
  else:out.append(s[i]);i+=1
 assert depth==0
 return ''.join(out)
names=[];records={};private=[]
for m in json.loads((B/'MODULES.json').read_text()):
 f=(B if m.startswith('Handoff') else B/'inputs')/(m+'.lean')
 s=strip_comments(f.read_text());ns=re.findall(r'^namespace\s+(\S+)',s,re.M);assert len(ns)==1
 decls=re.findall(r'^\s*(?:(private|protected|public)\s+)?(?:theorem|lemma)\s+([^\s({:\[]+)',s,re.M)
 decs=[n for vis,n in decls if vis!='private']
 private.extend({'module':m,'source_name':n} for vis,n in decls if vis=='private')
 assert not any('.' in n for n in decs)
 full=[ns[0]+'.'+n for n in decs];names+=full
 records[m]={'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'names':full}
names+=['LeanControls.UncertainLag.exact_initial','LeanControls.UncertainLag.exact_ode']
assert len(names)==len(set(names))==314
builder=json.loads((B/'verification.json').read_text())
assert set(builder['axioms'])==set(names)
assert len(private)==3 and all(x['module']=='ComparisonEnvelope' for x in private)
(R/'independent-audit-inventory.json').write_text(json.dumps({'method':'Remove nested block and line comments; inventory exported theorem and lemma commands, recording private helpers separately, in each single-namespace module; prime-capable name token. Add two original exact-flow closures explicitly.','modules':records,'full_names':names,'count':len(names),'builder_direct_audit_count':len(builder['axioms']),'private_helpers_checked_in_module_and_public_closures':private,'public_audit_matches':True},indent=2)+'\n')
print('Inventory:',len(names),'public audit names;',len(private),'private helpers already checked through module and public closures.')
