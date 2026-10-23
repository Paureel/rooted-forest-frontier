from pathlib import Path
import json,re,hashlib,difflib
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file())
def read(p):return {r['name']:r for line in p.read_text().splitlines() if line.startswith('GENERATED|') for r in [json.loads(line.split('|',1)[1])]}
a=read(H/'isolated-original-producers-v1/FreshGeneratedProducerDumpV1.adapter.log');b=read(H/'isolated-source-v1/FreshGeneratedProducerDumpV1.adapter.log');assert set(a)==set(b) and len(a)==15
mapping=dict(zip(['RMAF','Restriction','Embedding','Partition','Cost','Forward'],['RMAF','GroupRestriction','GroupEmbedding','GroupPartition','GroupCost','GroupForward']));comparisons=[];diffs=[]
for name in sorted(a):
 x,y=a[name],b[name];normalized=x['body'];replacements=0
 for old,new in mapping.items():
  if old!=new:normalized,n=re.subn(r'_private\.'+re.escape(old)+r'(?=[.\s])','_private.'+new,normalized);replacements+=n
 assert x['body']!='NONE' and y['body']!='NONE'
 assert x['type']==y['type'] and normalized==y['body'] and mapping[x['origin']]==y['origin'] and sorted(x['axioms'])==sorted(y['axioms']),name
 same=x['body']==y['body'];assert same or replacements==1
 if not same:diffs.extend(difflib.unified_diff(x['body'].splitlines(),y['body'].splitlines(),name+' original',name+' adapted',n=2))
 comparisons.append({'name':name,'original_origin':x['origin'],'adapted_origin':y['origin'],'type_exact':True,'body_raw_exact':same,'body_equal_after_only_explicit_private_producer_name_transport':True,'private_producer_name_occurrences_transported':replacements,'original_type_sha256':hashlib.sha256(x['type'].encode()).hexdigest(),'adapted_type_sha256':hashlib.sha256(y['type'].encode()).hexdigest(),'original_body_sha256':hashlib.sha256(x['body'].encode()).hexdigest(),'adapted_body_sha256':hashlib.sha256(y['body'].encode()).hexdigest()})
assert sum(x['body_raw_exact'] for x in comparisons)==12 and sum(not x['body_raw_exact'] for x in comparisons)==3
(H/'GENERATED-BODY-EXACT-DIFF-v2.txt').write_text('\n'.join(diffs)+'\n')
out={'verdict':'PASS_EXACT_GENERATED_PRODUCER_TYPE_AND_BODY_ADAPTERS','generated_count':15,'raw_equal_types':15,'raw_equal_bodies':12,'transported_private_prefix_bodies':3,'comparisons':comparisons,'full_exprs_retained_in_both_source_only_replay_logs':True,'source_modifications':0,'all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-generated-adapters-v2.json').write_text(json.dumps(out,indent=2)+'\n')
(H/'GENERATED-ADAPTER-STRICT-FAILURE-v1.json').write_text(json.dumps({'failed_assertion':'Initial normalizer required a dot after _private.Embedding. The actual Expr repr prints Lean.Name.mkNum `_private.Embedding 0, so three bodies remained unequal.','root_cause':'Representation delimiter at the exact private producer-module prefix; all 15 types and all other body bytes agree.','correction':'V2 permits dot or whitespace as the delimiter and transports only the six explicitly pinned producer module names. Exactly one occurrence changes in each of the three eq_def bodies.','failed_source':'generated_adapter_replay_v1.py','old_full_logs_preserved':True,'candidate_source_changes':0,'unexplained_differences':0},indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['verdict','generated_count','raw_equal_types','raw_equal_bodies','transported_private_prefix_bodies']}))
