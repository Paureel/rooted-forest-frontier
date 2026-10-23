#!/usr/bin/env python3
"""One-shot postcontact arithmetic/review-sheet controls. Zero new blind credit.
No author auditor, solver, oracle, or instrumented program is executed.
"""
from pathlib import Path
from fractions import Fraction
import datetime,gzip,hashlib,json,shutil,time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fixture=HERE/'ADAPTATION-CONTROLS-v1.json'
assert sha(fixture)=='e784a2b15040165ed6e721583fd075e66c13d72aeff2c493592a328934fcc18f'
f=json.loads(fixture.read_text());idx=json.loads((HERE/'LICENSE-INDEX-v1.json').read_text())
if shutil.disk_usage(HERE).free<3*1024**3:raise RuntimeError('diskfloor')
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');out=HERE/'adaptation-runs'/stamp;out.mkdir(parents=True)
shutil.copyfile(__file__,out/'runner.source.py');shutil.copyfile(fixture,out/'fixture.source.json')
events=[];start=time.monotonic()
def serialize(v):
 if isinstance(v,Fraction):return {'numerator':v.numerator,'denominator':v.denominator}
 if isinstance(v,dict):return {k:serialize(x) for k,x in v.items()}
 if isinstance(v,(tuple,list)):return [serialize(x) for x in v]
 return v
def case(name,actual,expected,kind='positive'):
 e={'name':name,'actual':serialize(actual),'expected':serialize(expected),'pass':actual==expected,'kind':kind};events.append(e)
 with (out/'cases.jsonl').open('a') as h:h.write(json.dumps(e,sort_keys=True)+'\n')
 if not e['pass']:raise AssertionError(name)
def reject(name,false_proposition):case(name,false_proposition,False,'corruption')
def meter(jobs,b,charges,fail):
 if not jobs:return [],2,0
 kind,key=jobs[0]
 if kind=='resolved':
  qs,caller,rec=meter(jobs[1:],b,charges,fail);return qs,caller+5,rec
 if key==fail:return [[key,b]],8,charges[key]
 qs,caller,rec=meter(jobs[1:],b,charges,fail);return [[key,b]]+qs,caller+8,charges[key]+rec
try:
 c=Fraction(*f['c']);gamma=Fraction(*f['gamma']);G=1/(1-2/c)
 for profile in f['profiles']:
  mass=sum((c**(-d) for d in profile['debits']),Fraction())
  case(profile['name'],[mass,mass<=gamma],[Fraction(*profile['expected']),True])
 case('diagonal-base3',Fraction(3)**-3+Fraction(3)**-4,Fraction(4,81))
 case('forest-geometric',[G,1+G*2/c==G],[Fraction(*f['geometric']),True])
 C=14*(4096*8**8)+4*(2*768+16*3**3)+2*(128*3**3+4*(256*32**3+6)+256)+12*(2*(4096*8**8)+256*6**4)+96
 case('monomial-intermediate-C',[C,C<=2**50],[f['monomial_intermediate_C'],True])
 grid=[]
 for M in range(f['monomial_grid']['M_first'],f['monomial_grid']['M_last']+1):
  inspect=4096*(7*M+1)**8;resource=2*M*(2*M+2)+2*M+1
  initial=128*(2*M+1)**3;cap=256*(resource+1)**3
  generation=initial+2*(cap+6)*(M+1)+M*(16*(2*M+3)*(2*M)+4*(M+1)+3)
  span=((16*(3*M+2)+16)*(2*M+1))*(2*M)
  overlap=(2*M)**2*(2*span+16*(2*M+1)**3)
  material=2*inspect+256*(M+2*M*M+2*M+1)**4
  poly=14*inspect+overlap+2*generation+12*material+32*(2*M+1)
  grid.append({'M':M,'polynomial':poly,'bound':2**50*M**8,'pass':poly<=2**50*M**8})
 case('monomial-grid',[len(grid),all(x['pass'] for x in grid)],[f['monomial_grid']['expected_cases'],True])
 (out/'monomial-grid.json').write_text(json.dumps(grid,indent=2)+'\n')
 nested=f['nested'];q=nested['q'];budgets=[q-d for d in nested['debits']]
 flat=sum((c**r for r in budgets),Fraction())/c**q
 case('flattened-once-frontier',flat,Fraction(*nested['expected_gamma']))
 spec=f['literal_meter_run'];qs,caller,rec=meter(spec['jobs'],spec['budget'],spec['charges'],spec['failure_key'])
 case('literal-failed-duplicate-stop',[qs,caller,rec,caller+rec],[spec['expected_queries'],spec['expected_caller'],spec['expected_recursive'],spec['expected_total']])
 sq,sc,sr=meter(spec['jobs'],spec['budget'],spec['charges'],None);twin=spec['success_twin']
 case('literal-success-twin',[sq,sc,sr,sc+sr],[twin['expected_queries'],twin['expected_caller'],twin['expected_recursive'],twin['expected_total']])
 called=[]
 def callback(key):called.append(key);return None if key=='X' else ['answer']
 answers=list(map(callback,f['direct']['jobs']))
 case('direct-first-failure-map',len(called),f['direct']['expected_evaluated'])
 case('hypothetical-absorption170',gamma*f['absorption']['sufficient_D']+1<=f['absorption']['sufficient_D'],True)
 bits=(2**f['bit_control']['numeric_label_exponent']).bit_length()
 case('count-does-not-bound-bits',[bits,bits>f['bit_control']['label_count']],[f['bit_control']['expected_label_bits'],True])
 sources={}
 for name in sorted({s['file'] for s in f['source_sentinels']}):
  p=ROOT/name
  if name not in idx or sha(p)!=idx[name]:raise RuntimeError('source/license hash mismatch '+name)
  data=p.read_bytes()
  if len(data)>64*1024**2 or max(map(len,data.splitlines()),default=0)>16*1024**2:raise RuntimeError('source caps')
  sources[name]=data.decode()
  snap=out/('source-'+str(len(sources))+'.lean');snap.write_bytes(data)
  with (HERE/'CONTACT-v1.jsonl').open('a') as h:h.write(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'event':'POSTCONTACT_CONTROL_SOURCE_SNAPSHOT','path':name,'sha256':idx[name],'snapshot':str(snap.relative_to(HERE)),'new_blind_credit':0})+'\n')
 def coverage(texts):return all(s['literal'] in texts[s['file']] for s in f['source_sentinels'])
 case('source-sheet14-sentinels',[len(f['source_sentinels']),coverage(sources)],[14,True])
 reject('retained-qminus2-mass',2/c+1/c**2<=1)
 reject('drop-base-upper-premise',Fraction(4)**-3+Fraction(4)**-4<=4*Fraction(4)**-4)
 reject('drop-inner-frontier-cap',2*flat<=1)
 reject('drop-budget-order',c**3==c**2*c**(-max(2-3,0)))
 reject('repeat-D-at-depth',2*gamma<=1)
 reject('absorb-at169',gamma*f['absorption']['insufficient_D']+1<=f['absorption']['insufficient_D'])
 reject('drop-duplicate',caller+rec==spec['drop_duplicate_claim'])
 reject('drop-failed',caller+rec==spec['drop_failed_claim'])
 reject('drop-direct-suffix',len(called)==f['direct']['drop_failure_suffix_claim'])
 reject('count-as-bit-cap',bits<=f['bit_control']['label_count'])
 for s in f['source_sentinels']:
  changed=dict(sources);changed[s['file']]=changed[s['file']].replace(s['literal'],'[DELIBERATE_OMISSION]')
  with gzip.open(out/('omit-'+s['key']+'.lean.gz'),'wt') as h:h.write(changed[s['file']])
  reject('omit-'+s['key'],coverage(changed))
 positive=sum(x['kind']=='positive' for x in events);negative=sum(x['kind']=='corruption' for x in events)
 assert [positive,negative]==[f['expected_positive_count'],f['expected_corruption_count']]
 result={'status':'ADAPTATION_CONTROLS_PASSED','positive':positive,'positive_expected':f['expected_positive_count'],'corruption_catches':negative,'corruptions_expected':f['expected_corruption_count'],'seconds':time.monotonic()-start,'fixture_sha256':sha(fixture),'runner_sha256':sha(Path(__file__)),'new_blind_credit':0,'sources':{name:idx[name] for name in sources},'scope':f['scope'],'global_base_main_novelty':'OPEN'}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print('ADAPTATION_CONTROLS_PASSED positives17/17 corruptions24/24; monomial grid63/63')
 print('No author execution. Zero new blind credit; global runtime remains OPEN.')
 print(str(out))
except BaseException as error:
 (out/'failure.json').write_text(json.dumps({'status':'FAILED','error':repr(error),'events_completed':len(events)},indent=2)+'\n')
 raise
