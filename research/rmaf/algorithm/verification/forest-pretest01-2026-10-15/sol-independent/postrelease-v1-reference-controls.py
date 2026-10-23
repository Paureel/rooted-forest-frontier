#!/usr/bin/env python3
"""Targeted postcontact controls for DAG dependency extraction, no new blind credit."""
import ast
import copy
import json
from pathlib import Path
import signal
import time

HERE=Path(__file__).resolve().parent
signal.alarm(30)
start=time.perf_counter()
parsed=ast.parse((HERE/'postrelease-v1-origin-analysis-v3.py').read_text())
nodes=[node for node in parsed.body if isinstance(node,ast.FunctionDef)
       and node.name in ('require','name_string','expression_refs')]
namespace={}
exec(compile(ast.Module(body=nodes,type_ignores=[]),'extracted_own_reference_functions','exec'),namespace)
nat=['str',['anonymous'],'Nat']
structure=['str',['str',['anonymous'],'PlantProjection'],'Struct']
clean={'nodes':[['const',nat,[]],['proj',structure,0,0]],'root':1,'refs':['Nat']}
references,augmented=namespace['expression_refs'](clean,{})
assert references=={'Nat','PlantProjection.Struct'} and augmented=={'PlantProjection.Struct'}
checks=[{'id':'projection_structure_reference','clean_pass':True,'broken_const_only_extractor_caught':
         references!={'Nat'}}]
for name,mutation in [('future_child',lambda d:d['nodes'][1].__setitem__(3,1)),
                      ('fabricated_auxiliary_reference',lambda d:d['refs'].append('PlantHidden.axiom'))]:
    corrupt=copy.deepcopy(clean);mutation(corrupt);caught=False
    try:namespace['expression_refs'](corrupt,{})
    except AssertionError:caught=True
    assert caught,name
    checks.append({'id':name,'clean_twin_pass':True,'corruption_caught':True})
out=HERE/'postrelease-v1-reference-controls.json';assert not out.exists()
out.write_text(json.dumps({'status':'PASS','checks':checks,'seconds':time.perf_counter()-start,
                           'timing':'postcontact extension controls; no new independent replication credit'},indent=2)+'\n')
print(json.dumps({'status':'PASS','controls':len(checks),'seconds':time.perf_counter()-start}))
