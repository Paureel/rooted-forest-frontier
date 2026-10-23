#!/usr/bin/env python3
from pathlib import Path
import json,importlib.util
H=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_std_api',H/'frozen-ready-v1/std_toy_gates.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.F=H/'isolated-release-v1';a.OUT=a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-interface-gates-v3.json'
p=a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-interface-gates-v2.json';old=json.loads(p.read_text());assert old['verdict']=='OPEN-INTERFACE-GATE-FAILURE' and sum(x['false_propositions_rejected'] for x in old['false_controls'].values())==5
mods=json.loads((a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-source-rebuild-v1.json').read_text())['order']
a.state={'runs':[],'audits':{},'prior_v2_receipt_sha256':a.sha(p),'false_controls':old['false_controls'],'failed_proof_and_diagnostic_attempts_retained':True,'all_main_milestones':'OPEN'}
try:
 p=H/'PretestSlotsV2.lean';(a.F/p.name).write_bytes(p.read_bytes());a.compile('PretestSlotsV2');rows=a.audit('FreshFinalOriginAudit',mods+['PretestSlotsV2'],mods+['PretestSlotsV2']);assert len(rows)>=2042 and not any(r['rejected'] for r in rows)
 q=a.F/'FreshChangedPretestV3.txt';original=a.F/'Pretest.lean';want='b1c811c03315de68dee43b2201c5d824a463b317024cd11679ff75c5ff5a4eba';assert a.sha(original)==want;q.write_bytes(original.read_bytes()+b'\n-- changed byte plant\n');assert a.sha(q)!=want
 a.state['source_pin_plant']={'expected_sha256':want,'clean_matches':True,'corrupted_sha256':a.sha(q),'corruption_rejected':True}
 a.state['verdict']='PASS-EXACT-INTERFACES-FIVE-FALSE-CLAIMS-AND-ORIGINAL-PAIR-SLOT-SEAM';a.save();print(json.dumps({'verdict':a.state['verdict'],'complete_origins':len(mods)+1,'declarations':len(rows)}))
except Exception as e:a.state['verdict']='OPEN-FINAL-INTERFACE-FAILURE';a.state['error']=repr(e);a.save();raise
