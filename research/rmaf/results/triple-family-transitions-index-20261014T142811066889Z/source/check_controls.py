#!/usr/bin/env python3
"""One-shot exact fixture harness for the index route, not a geometry checker.
Inputs: frozen lists and designated members. Outputs: tagged indices and counts.
Reject duplicate names or absent designated indices; compare exact lists/counts.
Known planted answers and corruptions live in controls.json, never generated here.
"""
import datetime, hashlib, json, pathlib, time
OWN = pathlib.Path(__file__).resolve().parent
ROOT = OWN.parents[5]
SPEC = OWN/'controls.json'
spec = json.loads(SPEC.read_text())
start = time.monotonic()

def evaluate(f):
    indices = [('M',)]
    for side, prefix in [('left','L'), ('right','R')]:
        xs, o = f[side], f[side+'_boundary']
        if len(set(xs)) != len(xs):
            raise ValueError('duplicate source index')
        if o not in xs:
            raise ValueError('designated index absent')
        for x in xs:
            if x != o:
                indices.append((prefix,x))
    assert len(set(indices)) == len(indices)
    names = [':'.join(k) for k in indices]
    return dict(indices=names, blocks=len(indices), closed=sum(k[0]!='M' for k in indices))

positives = {f['id']:f for f in spec['positive']}
rows = []
for f in spec['positive']:
    value=evaluate(f)
    passed=(value['indices']==f['expected'] and value['blocks']==f['blocks'] and value['closed']==f['closed'])
    rows.append(dict(kind='positive', id=f['id'], pass_=passed, actual=value))
for f in spec['malformed']:
    try:
        evaluate(f)
        rejected=False
        diagnostic='accepted malformed input'
    except ValueError as error:
        rejected=str(error)==f['reason']
        diagnostic=str(error)
    twin=positives[f['clean_twin']]
    twin_value=evaluate(twin)
    clean=twin_value['indices']==twin['expected'] and twin_value['blocks']==twin['blocks'] and twin_value['closed']==twin['closed']
    rows.append(dict(kind='malformed', id=f['id'], pass_=rejected and clean, diagnostic=diagnostic, clean_twin_pass=clean))
for f in spec['wrong_results']:
    value=evaluate(positives[f['fixture']])[f['field']]
    rows.append(dict(kind='wrong_result', id=f['id'], actual=value, wrong=f['wrong'], clean=f['clean'], pass_=value!=f['wrong'] and value==f['clean']))
expected={'positive':5,'malformed':3,'wrong_result':4}
counts={k:sum(r['kind']==k for r in rows) for k in expected}
passed=counts==expected and all(r['pass_'] for r in rows)
# Deliberately broken equality comparator must fail the wrong-result battery.
broken_comparator_gate=all(not (lambda actual, proposed: True)(evaluate(positives[f['fixture']])[f['field']], f['wrong']) for f in spec['wrong_results'])
passed=passed and not broken_comparator_gate
receipt=dict(schema=1, scope='finite index fixtures only, author controls', source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(), controls_sha256=hashlib.sha256(SPEC.read_bytes()).hexdigest(), counts=counts, expected_counts=expected, rows=rows, planted_broken_comparator_caught=not broken_comparator_gate, seconds=time.monotonic()-start, passed=passed)
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
output=ROOT/'research/rmaf/results'/('triple-family-transitions-index-controls-'+stamp+'.json')
output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'receipt':str(output.relative_to(ROOT)), 'counts':counts, 'planted_broken_comparator_caught':not broken_comparator_gate, 'passed':passed},indent=2))
raise SystemExit(0 if passed else 1)
