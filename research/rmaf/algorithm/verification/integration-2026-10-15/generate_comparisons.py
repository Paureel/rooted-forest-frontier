#!/usr/bin/env python3
"""Adapt frozen literals to actual executable interfaces; no new oracle values."""
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BUILD = HERE / 'isolated'
controls = json.loads((HERE / 'CONTROL-PIN.json').read_text())['controls']

def lit(value):
    if isinstance(value, bool): return 'true' if value else 'false'
    if isinstance(value, int): return str(value)
    if isinstance(value, list): return '[' + ', '.join(lit(x) for x in value) + ']'
    raise TypeError(value)
def vertex(value): return lit([c == '1' for c in value])
def tree(value):
    return f'(.leaf {value})' if isinstance(value, int) else f'(.node {tree(value[0])} {tree(value[1])})'
def color(values):
    return '(fun x : Nat => ' + ''.join(f'if x = {i} then {v} else ' for i, v in enumerate(values)) + '0)'
def group(g): return '⟨' + vertex(g[0]) + ', ' + lit(g[1]) + ', ' + str(g[2]) + '⟩'
def gs(groups): return '[' + ', '.join(group(g) for g in groups) + ']'
def custom(value):
    if value[0] == 'g': return '(.leaf ' + group(value[1:]) + ')'
    return f'(.node {vertex(value[1])} {custom(value[2])} {custom(value[3])})'
def current(data):
    base = custom(data['current']) if 'current' in data else f'(fromTree {color(data["colors"])} [] {tree(data["tree"])})'
    return f'(normalize {base})' if data.get('normalize', True) else base
def code(s):
    n = 1
    for c in s: n = 2 * n + int(c)
    return n
def snapshot(root, groups): return [[code(root)]] + [[code(g[0]), g[2]] + g[1] for g in groups]

header = '''import Controls
namespace FreshIntegrationChecks
open RMAF Universal233.CoreGraph Universal233.CoreProgram Universal233.Integration
def rootOrigin : GTree → Vertex
  | .leaf g => g.origin
  | .node p _ _ => p
def choiceView : Choice → Nat × List Vertex
  | .finish => (0, [])
  | .one a => (1, [a.origin])
  | .two a b => (2, [a.origin, b.origin])
  | .refuse _ => (3, [])
def addressCode (p : Vertex) : Nat := p.foldl (fun n b => 2*n + if b then 1 else 0) 1
def stateSnapshot (t : GTree) : List (List Nat) :=
  [addressCode (rootOrigin t)] :: (groups t).map (fun g => [addressCode g.origin, g.color] ++ g.labels)
def probe (t : GTree) (d : List Group) (c : List Vertex) : Receipt :=
  ⟨[⟨stateSnapshot t, c⟩, ⟨d.map Group.labels, d.map Group.origin⟩], [], 1, 0, 0⟩
'''
lines, mapping = [header], []
counter = 0
def add(record, field, expression, expected):
    global counter
    counter += 1
    name = f'control_{counter:03d}'
    lines.append(f'theorem {name} : {expression} = {expected} := by decide\n')
    mapping.append({'theorem': f'FreshIntegrationChecks.{name}', 'control_id': record['id'],
                    'field': field, 'expected_from': 'frozen CONTROL-PIN.json literal or documented probe encoding',
                    'expression': expression, 'expected_lean_literal': expected})

exclusions = []
for r in controls:
    op, d, e = r['op'], r['input'], r['expected']
    start = counter
    if op == 'partition':
        add(r, 'partition', f'(RMAF.partitionCheck {lit(d["labels"])} {lit(d["blocks"])})', lit(e['partition']))
    elif op == 'embedding':
        add(r, 'embeddings', f'(RMAF.pairwiseEmbeddings {tree(d["tree"])} {lit(d["blocks"])})', lit(e['embeddings']))
    elif op == 'agreement':
        a, b = tree(d['left']), tree(d['right'])
        add(r, 'agreement', f'(RMAF.agreement {a} {b} {lit(d["blocks"])})', lit(e['agreement']))
        proper = f'((decide (leaves {a}).Nodup) && (decide (leaves {b}).Nodup) && (leaves {a}).all (fun x => (leaves {b}).contains x) && (leaves {b}).all (fun x => (leaves {a}).contains x))'
        add(r, 'proper_inputs', proper, lit(e['proper_inputs']))
    elif op == 'normalize':
        t = current(d)
        add(r, 'groups', f'(groups {t})', gs(e['groups']))
        add(r, 'root_origin', f'(rootOrigin {t})', vertex(e['root_origin']))
        add(r, 'idempotent', f'(decide (normalize {t} = {t}))', lit(e['idempotent']))
    elif op in ['erase', 'surviving_owner']:
        t = f'(erase {vertex(d["chosen"])} {current(d)})'
        expected_root = 'none' if e['root_origin'] is None else f'(some {vertex(e["root_origin"])})'
        add(r, 'root_origin', f'({t}.map rootOrigin)', expected_root)
        if 'groups' in e:
            add(r, 'groups', f'({t}.map groups)', 'none' if e['root_origin'] is None else f'(some {gs(e["groups"])})')
        else:
            exclusions.append({'control_id': r['id'], 'fields': ['surviving_owner'], 'reason': 'source partition owner construction is noncomputable; reviewed exact erasure owner theorem, no executable Boolean owner API'})
    elif op == 'choose':
        kind = {'finish': 0, 'one': 1, 'two': 2, 'refuse-unnormalized': 3}[e['kind']]
        origins = '[' + ', '.join(vertex(v) for v in e['origins']) + ']'
        add(r, 'kind/origins', f'(choiceView (choose {current(d)}))', f'({kind}, {origins})')
    elif op == 'attempt':
        t, g = current(d), group(d['group'])
        cuts = '[' + ', '.join(vertex(v) for v in d['cuts']) + ']'
        receipt = f'(attempt probe {t} [] {cuts} {g})'
        add(r, 'chosen_is_current_group', f'((groups {t}).contains {g})', lit(e['chosen_is_current_group']))
        add(r, 'current_origins_unique', f'(decide (origins {t}).Nodup)', lit(e['current_origins_unique']))
        add(r, 'chosen_origin_is_actual_edge', f'((Universal233.CoreGraph.subtree {tree(d["tree"])} {vertex(d["group"][0])}).isSome && !({vertex(d["group"][0])} == ([] : Vertex)))', lit(e['chosen_origin_is_actual_edge']))
        add(r, 'child_attempts', f'{receipt}.childAttempts', str(e['child_attempts']))
        if e['continuation_called']:
            output = ('[⟨' + lit(snapshot(e['next_root'], e['next_groups'])) + ', ' + '[' + vertex(d['group'][0]) + (', ' if d['cuts'] else '') + ', '.join(vertex(v) for v in d['cuts']) + ']⟩, '
                      + '⟨' + lit([d['group'][1]]) + ', [' + vertex(d['group'][0]) + ']⟩]')
            add(r, 'continuation_called/next_root/next_groups/forwarded detached and cuts', f'{receipt}.outputs', output)
            add(r, 'guard_outcome', f'{receipt}.refusals', '[]')
        else:
            refusal = {'root': 'attempt to cut original root', 'duplicate': 'duplicate original source cut', 'entire': 'attempt removed entire current source'}[e['guard_outcome']]
            add(r, 'continuation_called', f'{receipt}.outputs', '[]')
            add(r, 'guard_outcome', f'{receipt}.refusals', '[' + json.dumps(refusal) + ']')
    if start == counter:
        exclusions.append({'control_id': r['id'], 'fields': list(e), 'reason': 'original graph/support/cut/refinement relation is independently checked in all49 graph controls; no corresponding decidable release API; universal source statements reviewed separately'})

lines.append('end FreshIntegrationChecks\n')
source = BUILD / 'FreshComparisons.lean'
assert not source.exists()
source.write_text(''.join(lines))
stale = next(r for r in controls if r['id'] == 'attempt-stale-valid-edge-not-a-current-group')
overlap = next(r for r in controls if r['id'] == 'embedding-overlap-despite-disjoint-labels')
negative = BUILD / 'FreshComparisonsFalse.lean'
negative.write_text('import FreshComparisons\nopen RMAF Universal233.CoreProgram\n'
    + f'example : ((groups {current(stale["input"])}).contains {group(stale["input"]["group"])}) = true := by decide\n'
    + f'example : RMAF.pairwiseEmbeddings {tree(overlap["input"]["tree"])} {lit(overlap["input"]["blocks"])} = true := by decide\n')
payload = {'source': str(source.relative_to(ROOT)), 'assertions': counter,
           'controls_with_compiled_fields': len({r['control_id'] for r in mapping}),
           'mapping': mapping, 'unsupported_fields': exclusions,
           'false_controls': [stale['id'], overlap['id']],
           'pre_candidate_control_source_sha256': hashlib.sha256((HERE / 'CONTROL-PIN.json').read_bytes()).hexdigest(),
           'sources_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in [source, negative]},
           'scope': 'post-contact adapter of frozen literal expectations to actual released interfaces; no extra replication or original-component theorem'}
(HERE / 'COMPARISON-MAP.json').write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps({'assertions_generated': counter, 'controls_with_compiled_fields': payload['controls_with_compiled_fields'], 'independent_frozen_false_twins': 2}))
