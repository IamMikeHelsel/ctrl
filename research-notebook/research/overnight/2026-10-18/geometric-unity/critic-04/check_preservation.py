from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent;R=D.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={
 'research/overnight/2026-10-18/geometric-unity/builder-04':'861cd093c525217d7f9f04dbee0ff22889efd541e746bc7a82eeea9a20c4a8c9',
 'research/overnight/2026-10-18/geometric-unity/builder-03':'3a6f59f0b26b0b60541fbb7d913be8dfb5c61ee0d7e8b9e10f8c36a1ae3ccf24',
 'research/overnight/2026-10-18/geometric-unity/critic-03':'a6af23a3104a95e72aa5141ce327369a947d478eacf333600df052d07a0bb23c',
 'research/overnight/2026-10-18/geometric-unity/builder-02':'fab7240941cb89b4517fd2614160f7ebf122eff095b017f4676bd09cd94b792d',
 'research/overnight/2026-10-18/geometric-unity/critic-02':'7984208c7cd519eb42eceb8264d6047af00c0d5869548d1ad17e57fcf4895c73',
 'research/overnight/2026-10-18/geometric-unity/analyst-01':'0c667224d83d64fc6cd9b764e1a556da23e5c7f90ef462b5f5f35149e60f579e',
 'research/overnight/2026-10-18/geometric-unity/critic-01':'d525512033db6160c60ee77cc032a68e103253fa6604c620deb79077d4e640d3',
 'research/pods/2026-10-17/weinstein/complex-adjoint-04/builder':'c498ef42bd3d8c428a0dcab1c34d4ca1eb41e419d57a47f00fdb6eca18cb7e0e',
 'research/pods/2026-10-17/weinstein/complex-adjoint-04/grader':'6c429ab23ededc5e5560d9b20cc0a957945e6b0c26dbeb49cc06ab9b79e4a6b8'}
results={}
for rel,expected in pins.items():
 folder=R/rel;assert sha(folder/'SHA256SUMS')==expected
 rows=(folder/'SHA256SUMS').read_text().splitlines()
 for row in rows:
  h,f=row.split('  ',1);assert sha(folder/f)==h,(rel,f)
 results[rel]={'manifest_sha256':expected,'files':len(rows)}
ledger=json.loads((D.parent/'builder-04/source-ledger.json').read_text())
for m,item in ledger['inherited_real'].items():
 assert sha(R/item['source'])==item['sha256']==sha(D.parent/'builder-04'/(m+'.lean'))
a=ledger['complex_bar'];assert sha(R/a['source'])==a['sha256']==sha(D.parent/'builder-04/ComplexAdjoint.lean')
assert sha(R/'research/weinstein-lean/operator-audit/source.pdf')=='3f28d742234a9841fc8e51ff172053200aa3eddf3ece38154a3328b9ebd186d4'
for f,h in ledger['library_sources'].items():assert sha(R/'lean-controls/.lake/packages/mathlib'/f)==h
out={'status':'PASS','manifests':results,'files_checked':sum(v['files'] for v in results.values()),'inherited_real_exact_copies':17,'inherited_complex_bar_exact_copy':True,'primary_pdf_sha256':sha(R/'research/weinstein-lean/operator-audit/source.pdf'),'library_source_hashes_match_builder_ledger':True}
(D/sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS','manifests':len(results),'files':out['files_checked']}))
