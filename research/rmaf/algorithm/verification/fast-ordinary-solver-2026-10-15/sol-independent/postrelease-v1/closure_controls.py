"""Known actual stored closure positive/negative controls, before real roots."""
import json,pathlib
from check_semantics import receipt
HERE=pathlib.Path(__file__).resolve().parent
expect={'closure-control-clean':[],
 'closure-control-hidden':['_private.PAxiom.0.PrecontactAxiom.hidden'],
 'closure-control-sorry':['sorryAx']}
for label,axs in expect.items():
 rows=receipt(label);assert rows[0]['record']=='root-set' and rows[-1]['record']=='actual-axiom-closure'
 assert rows[-1]['axioms']==axs and not rows[-1]['cached_axiom_extension_used']
 ds={r['name']:r for r in rows[1:-1]};assert len(ds)==rows[-1]['declarations']
 for r in ds.values():assert set(r['refs'])<=set(ds),'missing actual dependency'
 if label.endswith('hidden'):
  assert 'PrecontactAxiom.opaqueData' in ds and '_private.PAxiom.0.PrecontactAxiom.neverUsed' not in ds
 if label.endswith('clean'):assert 'PrecontactClean.helper' in ds and 'PrecontactClean.datum' in ds
try:
 broken=receipt('closure-control-hidden');broken[-1]['axioms']=[]
 assert broken[-1]['axioms']==expect['closure-control-hidden']
except AssertionError:pass
else:raise AssertionError('axiom comparator blind')
result={'status':'ACTUAL-CLOSURE-CONTROLS-PASS','positive_axioms':expect,'forged_empty_axiom_union_rejected':True,
 'actual_opaque_and_proof_dependencies_checked':True,'postcontact_extension':True,'new_blind_replication_credit':False}
(HERE/'CLOSURE-CALIBRATION-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,sort_keys=True))
