#!/usr/bin/env python3
"""One-shot evidence consistency checks; no solver/oracle execution."""
import hashlib, json, pathlib

here = pathlib.Path(__file__).resolve().parent
root = here.parents[5]
graph = json.loads((here/'DEPENDENCY-GRAPH-v2.json').read_text())
plant = json.loads((here/'PLANT-DEPENDENCY-GRAPH-v1.json').read_text())
stored = json.loads((here/'OWN-STORED-BODIES-v2.json').read_text())
pins = json.loads((here/'PINNED-OBJECTS-v1.json').read_text())
checks = []
def check(name, condition, detail):
    checks.append(dict(name=name, passed=bool(condition), detail=detail))
check('forbidden closure absent', graph['forbidden_reached'] == [], graph['forbidden_reached'])
check('unknown body/metadata absent', graph['unknown'] == [], graph['unknown'])
check('standard three axioms', set(graph['axioms']) == {'Quot.sound','propext','Classical.choice'}, graph['axioms'])
check('no partial/unsafe proof dependency', all(not r['is_partial'] and not r['is_unsafe'] for r in graph['rows']), len(graph['rows']))
check('stored own producer bodies', all(r['body_raw'] is not None for r in stored if r['kind'] in ('theorem','definition','opaque')), len(stored))
check('transitive marker detected', plant['forbidden_reached'] == ['OwnHigh.auditForbiddenMarker'] and plant['unknown'] == [], plant['forbidden_reached'])
negative = (here/'Corruption27.log').read_text()
check('six false controls rejected', negative.count('error: Tactic `decide` proved that the proposition') == 6 and negative.count('is false') == 6, 6)
accepted = ['Controls13','Geometry15','Geometry17','Endpoint18','Forest21','EndpointRight22','Shared23','Restriction25','Boundary26','SourceControls28','Audit32','AuditPlant31']
for name in accepted:
    receipt = json.loads((here/(name+'.receipt.json')).read_text())
    check(name+' Lean receipt', receipt['returncode'] == 0 and receipt['guard_failure'] is None and (here/(name+'.olean')).exists(), receipt)
check('original pin inventory matched', pins['all_match'], dict(count=pins['count'], sha256=pins['manifest_sha256']))
rows = {r['name']:r for r in graph['rows']}
def closure(name):
    todo, seen = [name], set()
    while todo:
        n=todo.pop()
        if n in seen: continue
        seen.add(n)
        todo.extend(rows[n]['refs'])
    return seen
reused_lemma = 'RestrictionBridge.root_not_prepend'
sub = closure(reused_lemma)
check('reused list fact closure contains no other domain proof',
      all(rows[n]['kind'] != 'theorem' or rows[n]['module'].startswith(('Init','Std','Lean')) or n == reused_lemma for n in sub),
      dict(name=reused_lemma, module=rows[reused_lemma]['module'], closure_count=len(sub)))
out = dict(version=1, status='OPEN_SOURCE_BOUNDARY_OBLIGATION', all_checks_passed=all(c['passed'] for c in checks),
           checks=checks, accepted_source_basenames=accepted, no_literal_dichotomy_proof=True,
           no_counterexample_obtained=True)
(here/'FINAL-VALIDATION-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],all_checks_passed=out['all_checks_passed'],checks=len(checks),
                     graph_nodes=len(graph['rows']),own_producers=len(stored),reused_list_fact_closure=len(sub))))
raise SystemExit(0 if out['all_checks_passed'] else 1)
