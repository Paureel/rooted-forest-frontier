"""Planted fixed-environment shard controls; no candidate values used."""
import copy,gzip,json,pathlib
from scan_rows import read_label
from row_audit_metadata import rows,source_gate
HERE=pathlib.Path(__file__).resolve().parent
f=json.loads((HERE/'FIXED-ENV-CONTROLS-v1.json').read_text())
whole=read_label('fixed-whole');clean=read_label('fixed-clean');axiom=read_label('fixed-axiom')
assert whole[0]['fixed_entrypoint']==clean[0]['fixed_entrypoint']==axiom[0]['fixed_entrypoint']==f['entrypoint']
assert whole[0]['module_counts']==f['expected_counts']
get=lambda rr:{r['name']:r for r in rr[1:] if 'record' not in r}
w=get(whole);c=get(clean);a=get(axiom)
assert len(w)==7 and not(set(c)&set(a)) and w=={**c,**a}
ds,_=rows(whole);assert sum(r['kind']=='axiom' for r in ds.values())==2
try:source_gate(ds)
except ValueError:pass
else:raise AssertionError('private unused axiom gate failed in whole environment')
caught=[]
for name,bad in [('missing-row',whole[:-1]),('duplicate-row',whole+[copy.deepcopy(whole[1])])]:
 # Remove a declaration, not an arbitrary trailing trusted-boundary row.
 if name=='missing-row':
  bad=copy.deepcopy(whole);bad.pop(next(i for i,r in enumerate(bad) if r.get('kind')=='definition'))
 try:rows(bad)
 except ValueError:caught.append(name)
 else:raise AssertionError('row corruption escaped')
for label,reason in [('fixed-duplicate','duplicate selectors'),('fixed-unloaded','selector not loaded'),('fixed-empty','empty selectors')]:
 receipts=[json.loads(p.read_text()) for p in (HERE/'evidence').glob('*.json') if json.loads(p.read_text())['label']==label]
 assert len(receipts)==1;r=receipts[0];assert r['returncode']!=0 and r['stop_reason'] is None
 raw=b''.join(gzip.open(HERE/s['path'],'rb').read() for s in r['shards'])
 assert reason.encode() in raw;caught.append(label)
result={'status':'FIXED-ENVIRONMENT-CONTROLS-PASS','whole_declarations':7,'split_union_exact':True,
 'explicit_empty_module_count':0,'private_unused_axioms_detected':2,'caught':caught,
 'postcontact_extension':True,'new_blind_replication_credit':False}
(HERE/'FIXED-ENV-CALIBRATION-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,sort_keys=True))
