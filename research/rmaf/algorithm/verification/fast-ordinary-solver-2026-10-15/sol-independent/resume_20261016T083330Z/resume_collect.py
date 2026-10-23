"""One-shot label-routing continuation of the existing calibrated collector.
No declaration, reference, body, flag, module or refusal check is changed.
The frozen old collector is reused; only interrupted-shard receipt names differ.
"""
import copy,hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent
OLD=HERE.parent/'postrelease-v1'
sys.path.insert(0,str(OLD))
import collect_fixed_audits as old
from row_audit_metadata import rows,source_gate
from scan_rows import read_label
MAP={f'cold-fixed-b{i:03d}':f'cold-resume-fixed-b{i:03d}' for i in range(11,23)}
def route(label):return read_label(MAP.get(label,label))
def controls():
 # Same exact routing operation on already executed own synthetic full-path controls.
 def routed(label,mapping):return read_label(mapping.get(label,label))
 clean=routed('request',{'request':'fixed-clean'})
 assert clean==read_label('fixed-clean')
 ds,info=rows(clean);source_gate(ds);assert len(ds)==3
 caught=[]
 for kind,rr in [('missing-row',copy.deepcopy(clean)),('duplicate-row',copy.deepcopy(clean))]:
  if kind=='missing-row':rr.pop(next(i for i,r in enumerate(rr) if r.get('kind')=='definition'))
  else:rr.append(copy.deepcopy(rr[1]))
  try:rows(rr)
  except (ValueError,AssertionError):caught.append(kind)
  else:raise AssertionError('routing comparator corruption escaped')
 try:routed('request',{'request':'missing-synthetic-request'})
 except ValueError:caught.append('missing-label')
 else:raise AssertionError('missing label accepted')
 print(json.dumps({'status':'RESUME-LABEL-ROUTING-CONTROLS-PASS','clean_rows':len(ds),'caught':caught}))
 with (HERE/'LABEL-ROUTING-CALIBRATION-v1.json').open('x') as f:json.dump({'status':'PASS','clean_rows':3,'caught':caught,'map':MAP,'postcontact':True,'new_replication_credit':False},f,indent=2);f.write('\n')
def collect():
 assert (HERE/'LABEL-ROUTING-CALIBRATION-v1.json').exists()
 assert not (OLD/'FIXED-BODY-AUDIT-cold-v1.json').exists()
 old.read_label=route
 sys.argv=[sys.argv[0],'cold'];old.main()
 a=json.loads((OLD/'FIXED-BODY-AUDIT-cold-v1.json').read_text())
 b=json.loads((OLD/'FIXED-BODY-AUDIT-released-v1.json').read_text())
 keys=['module_fingerprints','structural','raw_flags','sorry_referrers','explicit_zero_declaration_modules']
 for k in keys:assert a[k]==b[k],k
 with (HERE/'FIXED-COLD-RELEASED-COMPARISON-v1.json').open('x') as f:json.dump({'status':'EXACT-RETAINED-ROW-FINGERPRINTS-MATCH','keys_compared':keys,'modules':a['modules'],'declarations':a['declarations'],'proof_text_equality_claimed':False,'full_raw_source_gate':a['full_raw_source_gate'],'partial_refusal_preserved':len(a['raw_flags']['partial']),'route_map':MAP,'new_replication_credit':False},f,indent=2);f.write('\n')
 print('EXACT RETAINED COLD/RELEASED ROW FINGERPRINTS MATCH; RAW PARTIAL REFUSAL PRESERVED')
if __name__=='__main__':
 if sys.argv[1]=='controls':controls()
 elif sys.argv[1]=='collect':collect()
 else:raise ValueError('mode')
