from pathlib import Path
import gzip,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/json.loads((D/'BUILD-v1.json').read_text())['directory'];C=B/'author-audit-v2/certificate.json';c=json.loads(C.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert c['status']=='PASS_AUTHOR_COMPLETE_HARD_PAID_SOURCE_UNIT_BOUND_REMAINING_HANDLERS_OPEN'
rows={}
for e in c['new_producers']:
 p=R/e['path'];assert sha(p)==e['sha256']
 for r in json.load(gzip.open(p,'rt')):rows[r['actual_name']]=r
prefix='OrdinaryDispatch.Hard2SourceWork.'
required={'generatedOutputsMeter':['OrdinaryDispatch.RecoveryLocalWork.meterGenerate'],
 'wholeOutputsMeter':[prefix+'generatedOutputsMeter','Universal233.WholeSourceWork.meterTagged'],
 'hardPaidSource':[prefix+'actualOutputsMeter',prefix+'fullOutputsSource'],
 'hardPaidSource_value':[prefix+'actualOutputsMeter_value',prefix+'fullOutputsSource_value'],
 'hardPaidSource_split':[prefix+'fullOutputsSource_split'],
 'hardPaidSource_bound':[prefix+'actualOutputsMeter_bound',prefix+'fullOutputsSource_local',prefix+'outputForestDebit_weighted','Universal233.Hard2PaidLocal.actual_paid_raw_mass',prefix+'binary_prefix_absorb']}
for short,refs in required.items():
 r=rows[prefix+short]
 assert all(ref in r['direct_references'] for ref in refs),(short,refs,r['direct_references'])
runtime=['generatedOutputsMeter','appendOutputsMeter','wholeOutputsMeter','sideTaggedMeter','kindOutputsMeter','edgeOutputsMeter','caseOutputsMeter','actualOutputsMeter','hardPaidSource','outputForestDebit']
for short in runtime:
 r=rows[prefix+short];assert r['kind']=='definition' and r['has_body'] and r['body']!='<none>'
 for ref in r['direct_references']:
  assert not any(x in ref for x in ['Classical.choose','minimumCallback','ExactSolverHyp','OrdinaryIH','CoreWork.meterGenerate','CoreWork.meterRun']),('RUNTIME_PROOF_OR_OLD_DECLARED_COST',short,ref)
assert len(c['version_compatibility'])==29
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
result=dict(status='PASS_AUTHOR_EXACT_HARD_PAID_INTERFACE_DEPENDENCY_GATE',audit=str(C.relative_to(R)),audit_sha256=sha(C),runtime=runtime,required_direct_references=required,independent_credit=0,all_global_native_milestones='OPEN')
(B/'INTERFACE-DEPENDENCY-GATE-v2.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
