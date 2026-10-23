#!/usr/bin/env python3
"""Timed fresh occurrence inventory of the already rebuilt pinned science."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
BUILD=HERE/'isolated-build-v1'
state=json.loads((HERE/'source-rebuild-v1.json').read_text())
mode=sys.argv[1]
if mode=='pilot':root='RMAF';origins=['RMAF']
elif mode=='full':
    assert state['full_passed'] and len(state['runs'])==143
    root='ReviewAll'
    origins=state['independent_topological_order']
    (BUILD/'ReviewAll.lean').write_text(''.join('import '+m+'\n' for m in origins))
else:raise ValueError('pilot/full')
env={**os.environ,'LEAN_PATH':str(BUILD)}
result={'mode':mode,'commands':[]}
out=HERE/('candidate-origins-'+mode+'-v1.json')
cmds=[]
if mode=='full':cmds.append([str(ROOT/'bootloops-lean'),'-o','ReviewAll.olean','ReviewAll.lean'])
cmds.append([str(ROOT/'bootloops-lean'),'--run',str(HERE/'producer_audit_v1.lean'),root,str(out),*origins])
try:
    for cmd in cmds:
        started=time.perf_counter()
        p=subprocess.run(cmd,cwd=BUILD,env=env,text=True,capture_output=True,timeout=60)
        result['commands'].append({'command':cmd,'returncode':p.returncode,'seconds':time.perf_counter()-started,
                                  'stdout':p.stdout,'stderr':p.stderr,'cwd':str(BUILD),'LEAN_PATH':str(BUILD)})
        assert p.returncode==0,'candidate origin audit failed'
    data=json.loads(out.read_text())
    rows=data['occurrences'];resolved=data['resolved_inventory']['records']
    keys=[(r['producer'],r['ordinal'],r['name']) for r in rows]
    assert len(keys)==len(set(keys))==data['occurrence_count'],'occurrence key/count mismatch'
    tallies={r['producer']:r['stored_count'] for r in data['producer_counts']}
    assert set(tallies)==set(origins),'missing requested scientific producer'
    assert all(sum(r['producer']==n for r in rows)==v for n,v in tallies.items()),'stored occurrence dropped'
    direct=[(r['producer'],r['name']) for r in rows if r['actual_is_direct_axiom'] or r['actual']['kind']=='axiom']
    unresolved=[(r['producer'],r['name'],r['unresolved_dependencies']) for r in rows if r['unresolved_dependencies'] or r['resolved'] is None]
    axioms=sorted({a for r in rows for a in r['actual']['axioms_resolved_name_closure']})
    actualAXrefs=sorted({a for r in rows for a in r['directAX_any_stored_producer']})
    result.update({'stored_occurrences':len(rows),'resolved_records':len(resolved),'unique_stored_names':len({r['name'] for r in rows}),
      'producer_modules':len(tallies),'private_occurrences':sum(r['name'].startswith('_private.') for r in rows),
      'actual_direct_custom_axioms':direct,'unresolved_actual_dependencies':unresolved,
      'resolved_name_axiom_union':axioms,'actual_body_directAX_any_stored_union':actualAXrefs,
      'actual_resolved_info_differences':[(r['producer'],r['name'],r['resolved_origin']) for r in rows if not r['actual_equals_resolved_info']],
      'json_bytes':out.stat().st_size})
    assert not direct and not unresolved,'custom axiom/unresolved occurrence remains unaccepted'
    assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},'nonstandard resolved axiom closure'
    assert set(actualAXrefs)<= {'propext','Classical.choice','Quot.sound'},'nonstandard actual direct axiom reference'
    result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:
    (HERE/('candidate-origin-run-'+mode+'-v1.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['commands','actual_resolved_info_differences']}))
