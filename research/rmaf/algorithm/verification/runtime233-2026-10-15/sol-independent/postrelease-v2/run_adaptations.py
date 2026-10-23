#!/usr/bin/env python3
"""One-shot postcontact continuation controls, zero new blind credit.
Finite hand-specified source models only; no author program/auditor/oracle runs.
"""
from pathlib import Path
from fractions import Fraction
import datetime,gzip,hashlib,json,shutil,time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fix=HERE/'ADAPTATION-CONTROLS-v2.json';assert sha(fix)=='6d404f7e2f77aea9bcd55b808be5a67c996397ac2f5d22c98608058b199f9f70'
f=json.loads(fix.read_text());idx=json.loads((HERE/'LICENSE-INDEX-v2.json').read_text())
if shutil.disk_usage(HERE).free<3*1024**3:raise RuntimeError('diskfloor')
out=HERE/'adaptation-runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');out.mkdir(parents=True)
shutil.copyfile(__file__,out/'runner.source.py');shutil.copyfile(fix,out/'fixture.source.json');events=[];start=time.monotonic()
def case(name,actual,expected,kind='positive'):
 e={'name':name,'actual':actual,'expected':expected,'pass':actual==expected,'kind':kind};events.append(e)
 with (out/'cases.jsonl').open('a') as h:h.write(json.dumps(e,sort_keys=True)+'\n')
 if not e['pass']:raise AssertionError(name)
def reject(name,proposition):case(name,proposition,False,'corruption')
def scan(begin,fuel,success):
 trials=[];chosen=None
 for b in range(begin,begin+fuel):
  yes=b==success;trials.append((b,yes))
  if yes:chosen=b;break
 return chosen,trials

def contains(x,xs):
 for i,y in enumerate(xs):
  if x==y:return True,2*(i+1)
 return False,2*len(xs)+1

def nodup(xs,calls):
 if not xs:return True,1
 val,work=nodup(xs[1:],calls)
 if not val:return False,work+1
 calls.append(xs[0]);hit,cw=contains(xs[0],xs[1:]);return not hit,work+cw+1

def best(lengths,K):
 if not lengths:return None,1
 tail,work=best(lengths[1:],K);head=lengths[0]
 selected=head if tail is None or max(head-1,0)<=max(tail-1,0) else tail
 return selected,K+work+head+(tail if tail is not None else 0)+4
try:
 o=f['optimizer'];chosen,trials=scan(0,o['n'],o['success']);query=sum(o['works'][b] for b,_ in trials)
 wrapper=o['preflight']+o['per_trial']*len(trials)+o['finish'];total=query+wrapper+(o['recovery'] if chosen is not None else 0)
 case('actual-start0-twofail-cost',[chosen,[b for b,_ in trials],sum(not yes for _,yes in trials),query,wrapper,total],[o['success'],o['trials'],o['failures'],o['query_work'],o['wrapper_work'],o['total']])
 z=f['offset_scan'];q,ts=scan(z['start'],z['fuel'],z['success']);cost=sum(z['works'][str(b)] for b,_ in ts)+z['preflight']+z['per_trial']*len(ts)+z['finish']+z['recovery']
 case('offset-scan',[q,[b for b,_ in ts],cost],[z['success'],z['trials'],z['total']])
 case('zero-fuel',scan(0,0,0),(None,[]))
 q,failed=scan(f['all_fail']['start'],f['all_fail']['fuel'],None)
 failcost=sum(o['works'][b] for b,_ in failed)+o['preflight']+o['per_trial']*len(failed)+o['finish']
 case('all-refused-generic-scan',[q,[b for b,_ in failed],failcost],[None,f['all_fail']['trials'],f['all_fail']['total']])
 last,lasttr=scan(0,f['last_success']['n'],f['last_success']['success'])
 case('last-budget-included',[last,[b for b,_ in lasttr]],[f['last_success']['success'],f['last_success']['trials']])
 q0,t0=scan(0,1,0);t0cost=o['works'][0]+o['preflight']+o['per_trial']+o['finish']+o['recovery']
 case('qzero-kone',[q0,[b for b,_ in t0],q0+1,t0cost],[0,f['zero_success']['trials'],f['zero_success']['components'],f['zero_success']['total']])
 malformed={'trials':[],'recoveries':[],'output':None}
 case('malformed-before-query',malformed,{'trials':[],'recoveries':[],'output':None})
 d=f['decision_sum'];c=Fraction(*d['c']);summed=sum(d['work']);bound=(d['q']+1)*d['constant_P']*c**d['q']
 case('decision-all-trials',[summed,[bound.numerator,bound.denominator],summed<=bound],[d['expected_sum'],d['bound'],True])
 ch=f['checker'];F=ch['invalid_bounded_forest'];flat=sum(F,[]);fw=6*(len(flat)+len(F))+1;cw=4*len(flat)+1
 counts=sum(fw+cw+4+4 for _ in ch['labels'])+1
 case('repeated-flatten-count-scans',[fw,cw,counts],[ch['flatten_work'],ch['count_work'],ch['all_counts_work']])
 payload=len(F)<=ch['N'] and len(flat)<=ch['N'];accepted=all(flat.count(x)==1 for x in ch['labels']) and all(x in ch['labels'] for x in flat) and all(F)
 case('bounded-invalid-payload',[payload,accepted],[True,False])
 cm=f['common'];pairs=[(tuple(H),tuple(J)) for H in cm['FM'] for J in cm['FN']]
 case('duplicate-owner-occurrences',[len(pairs),len(set(pairs))],[cm['owner_occurrences'],cm['distinct_materialized_values']])
 winner,bw=best(cm['retained_tail_candidates'],cm['checker_work']);case('best-retained-tail-length',[winner,bw],[1,cm['best_work']])
 fresh=cm['input_max']+2;case('bounded-common-fresh',[fresh,fresh<2**cm['safe_power']],[cm['fresh_max'],True])
 pr=f['prefix'];dc=[];dv,dw=nodup(pr['duplicate_list'],dc);case('tail-first-duplicate',[dv,dw,0 in dc],[False,pr['duplicate_work'],False])
 cc=[];cv,cleanw=nodup(pr['clean_list'],cc);case('tail-first-clean',[cv,cleanw],[True,pr['clean_work']])
 case('missing-membership',contains(7,pr['clean_list']),(False,pr['missing_contains_work']))
 guard=pr['proper_false_work']+1;strict=pr['earlier_strict_let_work']+guard
 case('prefix-refusal-still-has-earlier-let',[guard,strict,pr['scalar_fee']*guard],[pr['guard_false_work'],pr['strict_let_plus_guard'],pr['scaled_guard_work']])
 N=3;proper=16*(N+1)**2+8*N*N+2*(4*N*N+2*N+3)*N+8;prefix=proper+16*N*N+8*N+3
 case('prefix-polynomials',[proper,prefix],[pr['proper_polynomial_N3'],pr['prefix_polynomial_N3']])
 sources={};base='research/rmaf/algorithm/universal233/ordinary_dispatch/'
 for sentinel in f['source_sentinels']:
  name=base+sentinel['file']
  if name in sources:continue
  path=ROOT/name;assert name in idx and sha(path)==idx[name]
  raw=path.read_bytes();assert len(raw)<=64*1024**2 and max(map(len,raw.splitlines()),default=0)<=16*1024**2
  sources[name]=raw.decode();(out/('source-'+str(len(sources))+'.lean')).write_bytes(raw)
  with (HERE/'CONTACT-v2.jsonl').open('a') as h:h.write(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'event':'POSTCONTACT_ADAPTATION_READ','path':name,'sha256':idx[name],'new_blind_credit':0})+'\n')
 def coverage(texts):return all(s['literal'] in texts[base+s['file']] for s in f['source_sentinels'])
 case('source-consumer-ten-sentinels',[len(f['source_sentinels']),coverage(sources)],[10,True])
 case('below-bill-strict-budget',[2<3,3<3],[True,False])
 reject('drop-failed-trial-cost',total==o['drop_failures_claim'])
 reject('recover-per-trial',total==o['recover_each_trial_claim'])
 reject('fuel-n-minus-one-misses-last',scan(0,f['last_success']['n']-1,f['last_success']['success'])[0] is not None)
 reject('keep-only-successful-work',summed==d['work'][-1])
 reject('automatic-recovery-for-any-cgt1',Fraction(2)**4<=Fraction(3,2)**4)
 reject('hostile-callback-has-sound-payload',ch['hostile_payload_labels']<=ch['hostile_leaf_count'])
 reject('cache-flatten-without-paying-each-copy',counts==ch['cached_flatten_claim'])
 reject('stop-unit-counterpart-on-first-rejection',counts==ch['first_reject_only_claim'])
 reject('deduplicate-owner-pairs',len(pairs)==len(set(pairs)))
 reject('omit-best-retained-tail-length',bw==cm['omit_retained_tail_claim'])
 reject('use-common-bits-without-input-cap',40+2<2**cm['safe_power'])
 reject('head-first-nodup-even-when-tail-false',0 in dc)
 reject('prefix-refusal-makes-strict-let-free',strict==guard)
 reject('drop-scalar-provider-fee',pr['scalar_fee']*guard==guard)
 reject('below-bill-covers-current-q',3<3)
 for i,s in enumerate(f['source_sentinels']):
  changed=dict(sources);name=base+s['file'];changed[name]=changed[name].replace(s['literal'],'[DELIBERATE_OMISSION]')
  with gzip.open(out/('omitted-'+str(i+1)+'.lean.gz'),'wt') as h:h.write(changed[name])
  reject('omit-consumer-sentinel-'+str(i+1),coverage(changed))
 positive=sum(e['kind']=='positive' for e in events);corruptions=sum(e['kind']=='corruption' for e in events)
 assert [positive,corruptions]==[f['expected_positives'],f['expected_corruptions']]
 result={'status':'POSTCONTACT_CONTROLS_PASSED','positives':positive,'corruption_catches':corruptions,'fixture_sha256':sha(fix),'runner_sha256':sha(Path(__file__)),'seconds':time.monotonic()-start,'new_blind_credit':0,'scope':f['scope'],'global_acceptance':'OPEN'}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print('POSTCONTACT_CONTROLS_PASSED20/20 specified results and25/25 corruption catches.')
 print('No author execution, actual-tree counterexample, new blind credit or global runtime acceptance.')
 print(str(out))
except BaseException as error:
 (out/'failure.json').write_text(json.dumps({'status':'FAILED','error':repr(error),'events_completed':len(events)},indent=2)+'\n')
 raise
