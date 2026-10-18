from pathlib import Path
import os,json,subprocess,datetime,shutil,tempfile,sys
HERE=Path(__file__).resolve().parent;dev=HERE/'development';cfg=json.loads((HERE/'development-env.json').read_text());bin=Path(cfg['bin']);env=os.environ.copy();env['PATH']=str(bin)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join([str(dev),*cfg['deps']]);name=sys.argv[1] if len(sys.argv)>1 else 'WeightedProfiles'
snap=Path(tempfile.mkdtemp(prefix='attempt-'+name+'-',dir=HERE));shutil.copyfile(HERE/(name+'.lean'),snap/(name+'.lean'));shutil.copyfile(HERE/(name+'.lean'),dev/(name+'.lean'))
proc=subprocess.run([str(bin/'lean'),'-o',name+'.olean',name+'.lean'],cwd=dev,env=env,text=True,capture_output=True,timeout=180);out=proc.stdout+proc.stderr;(snap/'compile.log').write_text(out);(snap/'run.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':proc.returncode,'module':name},indent=2)+'\n');print(str(snap));print(out);sys.exit(proc.returncode)
