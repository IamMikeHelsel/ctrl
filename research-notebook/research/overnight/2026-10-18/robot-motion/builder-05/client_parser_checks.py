from pathlib import Path
import json
import client

def main():
    cases=[]
    for value in ['0.57','.57',0.57,True,None,{},'1/0','1/2 extra','1); panic! "bad"','1/-2']:
        cases.append(('invalid_rational_'+repr(value),lambda value=value:client.rat(value)))
    for value in [-1,True,1.0,'7',None]:
        cases.append(('invalid_version_'+repr(value),lambda value=value:client.version(value)))
    cases += [('unexpected_field',lambda:client.keys({'x':1,'extra':2},['x'])),
      ('missing_field',lambda:client.keys({},['x'])),
      ('not_object',lambda:client.keys([],['x'])),
      ('bad_event',lambda:client.base({'events':[['0']],'offset':'0','width':'1/5','version':0}))]
    records=[]
    for name,call in cases:
        try: call()
        except (ValueError,ZeroDivisionError,TypeError) as e: records.append({'name':name,'rejected':True,'reason':str(e)})
        else: raise AssertionError(name+' unexpectedly passed')
    assert client.rat('2/4')=='(1/2:ℚ)' and client.rat('-3/2')=='(-3/2:ℚ)'
    out={'status':'PASS','rejected_invalid_inputs':len(records),'checks':records,
         'boundary':'tests of the Python input translation only; no formally verified parser claim'}
    (Path(__file__).parent/'client-parser-checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','rejected_invalid_inputs':len(records)}))
if __name__=='__main__':main()
