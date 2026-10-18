"""Frozen finite packet generator. No plant integration or tuning occurs here."""
from pathlib import Path
from fractions import Fraction as Q
from random import Random
import hashlib,json,shutil

HERE=Path(__file__).resolve().parent
ROBOT=HERE.parents[1]
SOURCE=ROBOT/'comparison-04/builder/frozen-fixed-streams.json'

def case_blobs(text):
    decoder=json.JSONDecoder();pos=text.index('[',text.index('"cases"'))+1;out={}
    while True:
        while text[pos].isspace() or text[pos]==',':pos+=1
        if text[pos]==']':return out
        obj,end=decoder.raw_decode(text,pos)
        out[obj['id']]=text[pos:end];pos=end

def packet(seq,observed,target):
    return {'sequence':seq,'observed_s':str(observed),'ready_s':str(observed+Q(1,50)),'target_m':str(target)}

def noise_case(name,times,values,zero_time,description):
    packets=[packet(100+i,t,v) for i,(t,v) in enumerate(zip(times,values))]
    packets.append(packet(100+len(times),zero_time,Q(0)))
    return {'id':name,'role':'primary','truth':[{'time_s':'0','position_m':'0'}],
            'packets':packets,'deadline_s':'7/2','end_s':'4','task':description+' Actual hold error <=0.2 mm throughout; endpoint tests at deadline.'}

def main():
    original=SOURCE.read_bytes();(HERE/'original-fixed-streams.json').write_bytes(original)
    text=original.decode();spec=json.loads(text);blobs=case_blobs(text)
    original_cases=[next(x for x in spec['cases'] if x['id']==name) for name in ['hold_jitter','persistent_goal']]
    times_a=[Q(1,5)+i*Q(3,50) for i in range(20)]
    gaps=[Q(x,100) for x in [2,6,4,8,2,10,6,4,2,8]]*2
    times_b=[Q(1,5)]
    for gap in gaps[:-1]:times_b.append(times_b[-1]+gap)
    zero_b=times_b[-1]+gaps[-1]
    times_cd=[Q(1,5)+i*Q(1,50) for i in range(80)]
    rng=Random(20261017)
    random_values=[Q(rng.randint(-1000,1000),1000000) for _ in range(80)]
    cases=original_cases+[
        noise_case('sign_60ms',times_a,[Q(1 if i%2==0 else -1,1000) for i in range(20)],times_a[-1]+Q(3,50),'Alternating signs every 60 ms; not the original 40 ms full-period signal.'),
        noise_case('irregular_alternation',times_b,[Q(1 if i%2==0 else -1,1000) for i in range(20)],zero_b,'Alternating signs with the declared two-cycle irregular gap list.'),
        noise_case('seeded_random',times_cd,random_values,times_cd[-1]+Q(1,50),'Seeded bounded random target errors; finite realized sample mean is reported.'),
        noise_case('biased_alternation',times_cd,[Q(1,2500)+Q(3 if i%2==0 else -3,5000) for i in range(80)],times_cd[-1]+Q(1,50),'Deliberate positive bias of .4 mm plus alternating .6 mm; true goal zero; not unbiased noise.')]
    result={k:v for k,v in spec.items() if k!='cases'}
    result['version']=2;result['cases']=cases
    encoded=json.dumps(result,indent=2)+'\n';new_blobs=case_blobs(encoded)
    for name in ['hold_jitter','persistent_goal']:
        assert new_blobs[name]==blobs[name],name
        (HERE/('original-'+name+'.json')).write_bytes(blobs[name].encode())
    (HERE/'packets.json').write_text(encoded)
    observations={case['id']:[{'observed_s':x['observed_s'],'ready_s':x['ready_s'],'target_m':x['target_m']} for x in case['packets']] for case in cases}
    (HERE/'observation-times.json').write_text(json.dumps(observations,indent=2)+'\n')
    metadata={'original_source':str(SOURCE),'original_file_sha256':hashlib.sha256(original).hexdigest(),'original_case_bytes_identical':{name:hashlib.sha256(blobs[name].encode()).hexdigest() for name in ['hold_jitter','persistent_goal']},
              'seed':20261017,'rng':'Python random.Random(seed).randint(-1000,1000), inclusive, exactly 80 calls','random_targets_rational':[str(x) for x in random_values],
              'random_sample_arithmetic_mean_m':str(sum(random_values,Q(0))/len(random_values)),
              'irregular_noise_observation_times':[str(x) for x in times_b],'irregular_final_zero_observation':str(zero_b),'irregular_gaps_to_zero':[str(x) for x in gaps],
              'stream_count':len(cases),'packet_counts':{x['id']:len(x['packets']) for x in cases}}
    (HERE/'input-provenance.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps({'streams':len(cases),'packets':metadata['packet_counts'],'irregular_observed_times':metadata['irregular_noise_observation_times']+[str(zero_b)],'random_sample_mean_m':metadata['random_sample_arithmetic_mean_m']},indent=2))

if __name__=='__main__':main()
