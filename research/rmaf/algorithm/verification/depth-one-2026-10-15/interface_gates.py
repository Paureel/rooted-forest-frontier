#!/usr/bin/env python3
"""Executable interface readouts, false propositions, and own original-pair slot seam."""
from pathlib import Path
import json,re,importlib.util
H=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_std_api',H/'frozen-ready-v1/std_toy_gates.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.F=H/'isolated-release-v1';a.OUT=a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-interface-gates-v1.json';a.state={'runs':[],'audits':{},'false_controls':{},'all_main_milestones':'OPEN'}
origin=a.ROOT/'research/rmaf/algorithm/universal233/depth_one'
statements='''import Runtime01
open RMAF Universal233.DepthOne Universal233.CutRealization
#print pretest01
#print proper
#print forest
#print sourceCuts
#print RealizedOutput
#check candidate_complete
#check source_two_split
#check proper_iff
#check refused_iff
#check found_globally_minimum
#check found_original_minimum
#check rejected_lower_bound
#check pretest_complete
#check literal_realization
#check candidate_count_original_edges
#check sameShapeCalls_bound
#check minimalVisits_bound
#print axioms candidate_complete
#print axioms found_original_minimum
#print axioms rejected_lower_bound
'''
try:
 (a.F/'FreshStatements.lean').write_text(statements);a.compile('FreshStatements')
 for name,count,kind in [('FalseControls',4,'false'),('FalseSourceColorV3',1,'false'),('FalseSourceColor',0,'ambiguous')]:
  p=origin/(name+'.lean');q=a.F/('Fresh'+name+'.lean');q.write_bytes(p.read_bytes());log=a.compile('Fresh'+name,kind)
  errors=re.findall(r'^Fresh'+name+r'\.lean:(\d+):\d+: error',log,re.M)
  if count:assert len(errors)==count,(name,errors,log)
  else:assert 'ambiguous' in log.lower()
  a.state['false_controls'][name]={'origin_sha256':a.sha(p),'copied_source_sha256':a.sha(q),'adapter':None,'false_propositions_rejected':count,'diagnostic_kind':kind,'error_lines':errors,'postproof':name!='FalseControls'};a.save()
 p=H/'PretestSlots.lean';(a.F/p.name).write_bytes(p.read_bytes());a.compile('PretestSlots');rows=a.audit('FreshSlotOriginAudit',['PretestSlots'],['PretestSlots']);assert rows and not any(r['rejected'] for r in rows)
 q=a.F/'FreshChangedPretest.txt';original=a.F/'Pretest.lean';want='b1c811c03315de68dee43b2201c5d824a463b317024cd11679ff75c5ff5a4eba';assert a.sha(original)==want;q.write_bytes(original.read_bytes()+b'\n-- changed byte plant\n');assert a.sha(q)!=want
 a.state['source_pin_plant']={'expected_sha256':want,'clean_matches':True,'corrupted_sha256':a.sha(q),'corruption_rejected':True}
 a.state['verdict']='PASS-EXACT-INTERFACES-FIVE-FALSE-CLAIMS-AND-ORIGINAL-PAIR-SLOT-SEAM';a.save();print(a.state['verdict'])
except Exception as e:a.state['verdict']='OPEN-INTERFACE-GATE-FAILURE';a.state['error']=repr(e);a.save();raise
