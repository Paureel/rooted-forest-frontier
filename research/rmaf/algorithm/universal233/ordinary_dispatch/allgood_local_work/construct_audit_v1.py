# One-shot consumer adapter of the frozen actual-source audit, engine unchanged.
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];S=D.parent/'ordinary_work_integration/audit_work_v1.py';T=D/'audit_dp_v1.py'
s=S.read_text();changes=[]
def edit(a,b):
 global s
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b);changes.append(dict(before=a,after=b))
edit("M=D.parent/'hard2_query_size/HARD2-SIZE-MANIFEST-v1.json'","M=D.parent/'ordinary_work_integration/HARD2-WORK-MANIFEST-v1.json'")
edit("'algorithm-universal233-ordinary-work-audit-'","'algorithm-universal233-allgood-local-work-audit-'")
edit("D/'build_components_v1.py',D/'extend_rule5_v1.py',B/'certificate-v1.json',B/'rule5-extension-v1/certificate.json'","D/'setup_source_v1.py',D/'extend_checker_v1.py',B/'SEED-RECEIPT.json',B/'checker-extension-v1/certificate.json'")
edit("'dbb5959912e70269374cb980a4e0501674bbf65829fb69e1a03b1ec87edf3e3b'","'337498c1f697edff18d0403616e62465e36a86192aeaba92916ef5643bd41932'")
edit("old['status']=='PASS_AUTHOR_ACTUAL_HARD2_QUERY_SIZE_SOURCE_PRODUCER'","old['status']=='PASS_AUTHOR_ACTUAL_HARD2_WORK_CONSUMER_SOURCE_PRODUCER'")
edit("base=json.loads((B/'certificate-v1.json').read_text());extension=json.loads((B/'rule5-extension-v1/certificate.json').read_text())","base=json.loads((B/'SEED-RECEIPT.json').read_text());extension=json.loads((B/'checker-extension-v1/certificate.json').read_text())")
edit("base['status']=='PASS_AUTHOR_WORK_COMPONENT_BUILD_PENDING_ACTUAL_CONSUMERS_AUDIT' and extension['status']=='PASS_AUTHOR_WORK_RULE5_EXTENSION_PENDING_ACTUAL_CONSUMER_AUDIT'","base['status']=='PASS_EXACT_READONLY_SOURCE_SEED' and extension['status']=='PASS_AUTHOR_DP_CHECKER_UNION_PENDING_CONSUMER_AUDIT'")
edit("for p,h in c['inputs'].items():assert sha(R/p)==h,('BUILD_INPUT_CHANGED',p)","for p,h in c.get('inputs',{}).items():assert sha(R/p)==h,('BUILD_INPUT_CHANGED',p)")
edit("own=['QueryProperBase','PairQueryProper','ModeQueryProper','Hard2QueryProper','Hard2Frontier','Hard2StepTrace','Hard2SourceBill','WorkControls']","own=['PaintCost','TableCost','OwnerCost','SolveCost','BlockCost','CandidateCost','GuardCost','Polynomial','DPControls']")
edit("r['module']=='WorkFalseControls'","r['module']=='DPFalseControls'")
edit("sha(D/'WorkFalseControls.lean')","sha(D/'DPFalseControls.lean')")
edit("(fp.parent/'WorkFalseControls.log')","(fp.parent/'DPFalseControls.log')")
edit("for r in c['runs']),('NO_UNION_SOURCE_RECEIPT',n)","for r in c.get('runs',[])),('NO_UNION_SOURCE_RECEIPT',n)")
edit("status='PASS_AUTHOR_ACTUAL_HARD2_WORK_CONSUMER_SOURCE_PRODUCER'","status='PASS_AUTHOR_ACTUAL_ALLGOOD_DP_SOURCE_WORK_PRODUCER'")
a=s.index("  interfaces=['OrdinaryDispatch.WorkIntegration.hard2Trace_value'");b=s.index(" save();print(rec['status']",a)
s=s[:a]+"""  interfaces=['AllGoodDP.LocalWork.meterChanges_value','AllGoodDP.LocalWork.meterBest_value','AllGoodDP.LocalWork.meterBest_work','AllGoodDP.LocalWork.meterTable_value','AllGoodDP.LocalWork.meterTable_work','AllGoodDP.LocalWork.meterOwner_value','AllGoodDP.LocalWork.meterSplit_value','AllGoodDP.LocalWork.meterCandidate_value','AllGoodDP.LocalWork.actual_paint_scalars','AllGoodDP.LocalWork.meterRun_value','AllGoodDP.LocalWork.actual_run_polynomial','AllGoodDP.LocalWork.refused_guard_work'],
  full_source_bit_payload_recurrence='OPEN',source_bill_runtime_correspondence='UNIT_SCALAR_REFERENCE_BODY_ONLY',scope='Literal full AllGoodDP.run structural source work: actual owner leaf/contains/index scans, tail-first best recomputing changes on both paint trees per comparison, table rows, chosen paint, split/raw/empty filter, proper and target-agreement guard. Value companions exact for all inputs; unit-work <=2^20*(n+1)^4 under actual proper state, rejected guard billed on malformed bounded-size inputs too. Numeric label/color/score caps derived. Full nonproof bodies retained and actual proof references traversed; exact finite source union only. Native scalar-bit/IR and total ordinary recurrence remain OPEN, same-author lineage, no independent acceptance.')
"""+s[b:]
# Additional positive native checks are sanity controls, never independent proof.
a=" rec['controls']['actual_false_claims']=dict(path=str(fp.relative_to(R)),sha256=sha(fp),errors=errs)\n"
assert s.count(a)==1
s=s.replace(a,a+" positive=[(p,c) for p,c in receipts if any(r['module']=='DPControls' and r['exit']==0 and r['source_sha256']==sha(D/'DPControls.lean') for r in c['runs'])];assert positive\n pp,pc=sorted(positive)[-1];plog=(pp.parent/'DPControls.log').read_text();assert re.findall(r'^(true|false)$',plog,re.M)==['true']*9\n rec['controls']['runtime_sanity']=dict(path=str(pp.relative_to(R)),sha256=sha(pp),count=9,independent=False)\n")
assert not T.exists();T.write_text(s)
(D/'AUDIT-CONSTRUCTION-v1.json').write_text(json.dumps(dict(reused_source=str(S.relative_to(R)),reused_source_sha256=hashlib.sha256(S.read_bytes()).hexdigest(),adapter_output_sha256=hashlib.sha256(T.read_bytes()).hexdigest(),exact_replacements=changes,final_scope_block_replaced=True,added_native_sanity_log_gate=True),indent=2)+'\n')
print('AUDIT_ADAPTER_WRITTEN',len(changes))
