#!/usr/bin/env python3
"""Actual released scientific declaration graph, with an injected-oracle control."""
import copy,json
from pathlib import Path
P=Path(__file__).resolve().parent
raw=json.loads((P/'candidate-audit-full-run1.json').read_text())
rows=raw['rows']; by={}
for r in rows:
    if r['name'] not in by or r['producer']==r['resolved_origin']: by[r['name']]=r
seeds=['cherries','candidates','select','makeChild','pendantChild','singletonChild','branches','terminalCut','endpointBranch','highBranch','remaining','childCall']
seeds=['Universal233.CherryBranching.'+n for n in seeds]
for n in seeds: assert n in by,n
forbidden={'RMAF.solve','RMAF.best','RMAF.assignments','RMAF.blocks','Universal233.CherryBranching.splitForest','BinaryExchange.splitAll','Universal233.CherryBranching.state_save_singleton'}
def closure(table,start):
    seen=set(); todo=[start]
    while todo:
        n=todo.pop()
        if n in seen: continue
        seen.add(n)
        if n in table: todo.extend(table[n]['references'])
    if seen&forbidden: raise ValueError('oracle/proof-surgery dependency: '+','.join(sorted(seen&forbidden)))
    return sorted(seen)
results=[{'seed':n,'reachable_scientific':[x for x in closure(by,n) if x in by],'all_names':len(closure(by,n))} for n in seeds]
planted=copy.deepcopy(by); planted[seeds[2]]['references'].append('RMAF.solve')
try: closure(planted,seeds[2])
except ValueError as ex: caught=str(ex)
else: raise AssertionError('injected optimum survived declaration graph check')
out={'status':'NO_REACHABLE_OPTIMUM_OR_PROOF_SURGERY','scope':'local executable declaration dependencies; supplied solver parameter remains external','seeds':results,'forbidden':sorted(forbidden),'injected_oracle_caught':caught}
(P/'runtime-dependency-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'seeds':len(results),'injected_oracle_caught':True}))
