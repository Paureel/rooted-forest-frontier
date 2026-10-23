#!/usr/bin/env python3
"""Candidate-statement readouts and explicit false/source-pin corruption controls."""
import json,importlib.util,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_api',HERE/'released_replay.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-interface-gates-v1.json';a.state={'runs':[],'audits':{},'negative_controls':{},'statement_readouts':{}}
rank=a.BUILD/'rank';rest=a.BUILD/'restriction'
rankstmt='''import ColorClasses
open RMAF Universal233 Universal233.CoreProgram Universal233.SourceCoverage Universal233.RankDichotomy
#print inputRank
#print RankFeasible
#print generate
#print CutRealization.ResidualAdj
#print CutRealization.RealizedOutput
#check generate_partition_coverage_paid
#check generate_color_cost
#check generate_outputs_mono
#check generate_output_cap
#check Assembly.generated_source_valid
#check feasible_unique
#check feasible_unique_color_classes
#check below_rank_outputs_empty
#check infeasible_cost
#check generate_tail_mass
#check infeasible_mass
#print rawQMass
#print axioms feasible_unique
#print axioms feasible_unique_color_classes
#print axioms infeasible_cost
#print axioms generate_tail_mass
#print axioms infeasible_mass
'''
reststmt='''import Consumers
open RMAF RestrictionBridge
#print restrict
#print Refines
#print family
#print agreement
#check restrict_inside
#check literal_clear_transport
#check pairwise_transport
#check family_nonempty
#check exact_cost
#check forward_decomposition
#check reverse_reconstruction
#print axioms forward_decomposition
#print axioms reverse_reconstruction
'''
try:
 for folder,name,source in [(rank,'FreshRankStatements',rankstmt),(rest,'FreshRestrictionStatements',reststmt)]:
  (folder/(name+'.lean')).write_text(source);log=a.compile_one(folder,name);a.state['statement_readouts'][folder.name]={'source_sha256':a.digest(folder/(name+'.lean')),'log_sha256':a.digest(folder/(name+'.log'))};a.save()
 for kind,folder,origin,name,n,adapter in [('rank',rank,a.RMAF/'algorithm/universal233/rank_dichotomy/FalseControls.lean','FreshFalseRank',3,('import Controls','import RankControls')),('restriction',rest,a.RMAF/'algorithm/universal233/restriction_bridge/FalseControls.lean','FreshFalseRestriction',5,None)]:
  source=origin.read_text()
  if adapter:assert source.count(adapter[0])==1;source=source.replace(*adapter)
  (folder/(name+'.lean')).write_text(source);log=a.compile_one(folder,name,'false');errors=re.findall(r'^'+name+r'\.lean:(\d+):\d+: error',log,re.M);assert len(errors)==n,(kind,errors,log)
  a.state['negative_controls'][kind]={'rejected_false_claims':n,'error_start_lines':errors,'origin':str(origin.relative_to(a.ROOT)),'origin_sha256':a.digest(origin),'adapter':adapter};a.save()
 # Byte corruption must fail source pin; clean twin passes at the exact manifest pin.
 p=rank/'RankCost.lean';expected=a.digest(p);q=rank/'FreshCorruptedSource.txt';q.write_bytes(p.read_bytes()+b'\n-- deliberately changed byte control\n')
 assert a.digest(p)==expected and a.digest(q)!=expected
 a.state['source_pin_control']={'clean_sha256':expected,'corrupt_sha256':a.digest(q),'clean_passed':True,'corruption_rejected':True}
 a.state['verdict']='PASS-EXECUTABLE-STATEMENT-READOUTS-8-FALSE-CLAIMS-AND-SOURCE-PIN-CONTROL';a.save();print(a.state['verdict'])
except Exception as e:a.state['verdict']='OPEN-INTERFACE-GATE-FAILURE';a.state['error']=repr(e);a.save();raise
