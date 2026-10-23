#!/usr/bin/env python3
"""One-shot retained-evidence audit; no scientific solver or new replication.

Emitall handles declarative quoted values; this wrapper supplies the missing
source/log hash and prior-audit reconciliation. It deliberately never imports
candidate code and never rewrites an existing receipt.
"""
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
RESULTS = ROOT / 'research/rmaf/results'
V = ROOT / 'research/rmaf/algorithm/verification'
BV = ROOT / 'research/rmaf/algorithm/balanced_safe_cover/verify'

def read(path):
    return json.loads((ROOT / path).read_text())

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def same(expected, observed):
    return expected == observed

def strip_comments(text):
    out = []
    pos = depth = 0
    while pos < len(text):
        if text[pos:pos+2] == '/-':
            depth += 1
            pos += 2
        elif depth and text[pos:pos+2] == '-/':
            depth -= 1
            pos += 2
        elif depth:
            pos += 1
        elif text[pos:pos+2] == '--':
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        else:
            out.append(text[pos])
            pos += 1
    assert depth == 0
    return ''.join(out)

# Post hoc plumbing plant for this hash/metadata audit only. It is not a new
# independent mathematical control or a replacement for the frozen controls.
plant = hashlib.sha256(b'known clean control').hexdigest()
assert same(plant, plant)
assert not same('0' * 64, plant)
controls = {'scope': 'post hoc hash comparator plumbing only',
            'clean_twin': same(plant, plant),
            'corrupt_expected_hash_caught': not same('0' * 64, plant)}

pins = []
def check_map(label, mapping):
    for path, expected in mapping.items():
        observed = sha(ROOT / path)
        pins.append(dict(group=label, path=path, expected=expected,
                         observed=observed, passed=same(expected, observed)))

for name in ['MACRO-DELIVERY-HASH-FREEZE.json', 'MACRO-SOURCE-FREEZE.json']:
    check_map(name, json.loads((V / name).read_text())['files'])
bm = read('research/rmaf/algorithm/paid_cover/DELIVERY-MANIFEST.json')
check_map('B original files', bm['files'])
check_map('B read dependencies', bm['read_dependencies'])
ba = read('research/rmaf/algorithm/paid_cover/DELIVERY-AMENDMENT-v2.json')
check_map('B amendment', ba['added_files'])
check_map('B original manifest identity', {ba['original_manifest']: ba['original_manifest_sha256']})

pre = json.loads((V / 'PRE-CANDIDATE-FREEZE.json').read_text())
independent = []
for name, expected in pre['files_sha256'].items():
    current = V / name
    archived = V / 'independent_graph-pre-candidate-v1.py' if name == 'independent_graph.py' else current
    independent.append(dict(name=name, frozen_sha256=expected,
                            current_sha256=sha(current),
                            preserved_frozen_copy=str(archived.relative_to(ROOT)),
                            preserved_frozen_sha256=sha(archived),
                            frozen_copy_matches=sha(archived) == expected))

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
lean = []
lr = read('research/rmaf/results/algorithm-review-lean-replay-and-axioms.json')
original_modules = {
    'RMAF': 'research/rmaf/lean/RMAF.lean',
    'FailedFrontier': 'research/rmaf/algorithm/paid_cover/FailedFrontier.lean',
    'Audit': 'research/rmaf/algorithm/paid_cover/Audit.lean',
    'MassChecks': 'research/rmaf/algorithm/paid_cover/MassChecks.lean',
    'ConditionalCover': 'research/rmaf/algorithm/joint_macro/ConditionalCover.lean',
    'Retarget233': 'research/rmaf/algorithm/Retarget233.lean',
}
for row in lr['rows']:
    name = row['module']
    p = V / 'lean-isolated' / (name + '.lean')
    log = p.with_suffix('.log')
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b', strip_comments(p.read_text()))
    parsed = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log.read_text(), re.S)
    inventory = [{'name': n, 'axioms': [x.strip() for x in deps.split(',') if x.strip()]} for n, deps in parsed]
    original = ROOT / original_modules[name]
    passed = (sha(p) == sha(original) == row['source_sha256'] and sha(log) == row['log_sha256']
              and inventory == row['axiom_inventory'] and len(inventory) == row['statements']
              and not forbidden and all(set(x['axioms']) <= allowed for x in inventory))
    lean.append(dict(group='A/B retained isolated audit', name=name,
                     original_source=original_modules[name],
                     source_sha256=sha(p), log_sha256=sha(log), statements=len(inventory),
                     axiom_inventory=inventory, forbidden=forbidden, passed=passed))
for row in lr['negative_controls']:
    p = V / 'lean-isolated' / (row['module'] + '.lean')
    log = p.with_suffix('.log')
    msg = log.read_text()
    lean.append(dict(group='A/B negative', name=row['module'],
                     source_sha256=sha(p), log_sha256=sha(log),
                     passed=msg == row['log'] and 'proved that the proposition' in msg and 'is false' in msg))

br = read('research/rmaf/results/algorithm-balanced-cover-verify-lean.json')
assert sha(BV / 'ReplayLean.py') == br['source_sha256']
for name in ['plants-v2', 'fixtures-v2', 'product-r2']:
    r = read(f'research/rmaf/results/algorithm-balanced-cover-verify-{name}.json')
    assert sha(BV / 'IndependentEdges.py') == r['source_sha256']
wr = read('research/rmaf/results/algorithm-balanced-cover-verify-witnesses.json')
assert sha(BV / 'ReplayWitnesses.py') == wr['source_sha256']
assert sha(BV / 'IndependentEdges.py') == wr['instrument_sha256']
for row in br['reports']:
    p = ROOT / row['source']
    isolated = BV / 'lean-isolated' / (row['name'] + '.lean')
    log = ROOT / row['log']
    msg = log.read_text()
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b', strip_comments(p.read_text()))
    prints = [line for line in msg.splitlines() if 'depends on axioms:' in line or 'does not depend on any axioms' in line]
    if row['expected_negative']:
        reason = ('evaluated to false' in msg or 'decide' in msg and ('failed' in msg or 'is false' in msg))
        semantics = row['returncode'] != 0 and reason and 'sorryAx' not in msg
    else:
        semantics = row['returncode'] == 0 and len(prints) == row['expected_print_count'] and prints == row['axiom_reports'] and set(row['axioms']) <= allowed
    passed = (sha(p) == row['source_sha256'] == sha(isolated) == row['isolated_source_sha256']
              and semantics and not forbidden and row['passed'])
    lean.append(dict(group='balanced/Q retained isolated audit', name=row['name'],
                     source=str(p.relative_to(ROOT)), source_sha256=sha(p),
                     log=str(log.relative_to(ROOT)), log_sha256=sha(log),
                     expected_negative=row['expected_negative'], statements=len(prints),
                     axioms=row['axioms'], forbidden=forbidden, passed=passed))

data = {}
for name in ['macro-common-n8', 'macro-deletion-family', 'macro-actual-emission-check',
             'paid-B1-B2-B3', 'paid-reserved-final', 'paid-every-child-progress', 'copy-bugreports']:
    data[name] = read(f'research/rmaf/results/algorithm-review-{name}.json')
a = data['macro-common-n8']
d = data['macro-deletion-family']
b = data['paid-B1-B2-B3']
children = data['paid-every-child-progress']
reserved = data['paid-reserved-final']
fixtures = read('research/rmaf/results/algorithm-balanced-cover-verify-fixtures-v2.json')['result']
product = read('research/rmaf/results/algorithm-balanced-cover-verify-product-r2.json')['result']
witness = read('research/rmaf/results/algorithm-balanced-cover-verify-witnesses.json')['result']
summary = {
 'A_common': {'residual': a['exact']['residual'], 'vector': a['vector'], 'mass': a['mass'],
              'admitted': a['prepared']['admitted'], 'earlier': a['prepared']['earlier'],
              'children_paid': [x['paid'] for x in a['children']]},
 'A_chain': {'tested': d['tested'], 'eligible_chains': d['eligible_chains'], 'refuters': d['refuters'],
             'scope': d['scope'], 'smallest_n': d['smallest']['n'],
             'exact': d['smallest']['exact_current_forest'],
             'edge_rows': [{k:v for k,v in x.items() if k != 'children'} for x in d['smallest']['chain_rows']]},
 'A_actual_emission': {'common_children': len(data['macro-actual-emission-check']['common_children']),
                       'chain_edge_pairs': len(data['macro-actual-emission-check']['chain_edge_pairs']),
                       'actual_stage_cut_checks': data['macro-actual-emission-check']['actual_stage_cut_checks']},
 'B_parent': b['exact_parent'],
 'B2': [{k:v for k,v in x.items() if k != 'witnesses'} for x in b['B2']],
 'B3': {k:v for k,v in b['B3'].items() if k != 'states'},
 'B_reserved': {'completed': reserved['completed'], 'passed': reserved['passed'],
                'eligible_initial_2e': reserved['eligible_initial_2e'],
                'all_children_completed_pairs': children['completed'],
                'all_children': sum(len(x['children']) for x in children['rows']),
                'every_reserved_pair_preserves_some_optimum': all(x['survival'] for x in children['rows'])},
 'B_copy_mutations': data['copy-bugreports'],
 'balanced_fixture_count': fixtures['fixture_count'],
 'balanced_equal_halves': {k:v for k,v in fixtures['equal_halves_n4'].items()
                          if not isinstance(v,(dict,list))},
 'balanced_product': [{k:v for k,v in x.items() if not isinstance(v,(dict,list))} for x in product['cases']],
 'Q_n6': {'optimum': witness['n6']['original']['optimum_cuts'],
          'optimum_realizations': witness['n6']['optimal_realization_count'],
          'onecuts': [{k:x[k] for k in ['isolated','tau','charged_total','lhs_tau','rhs_threshold','residual']} for x in witness['n6']['onecuts']],
          'twocut_repairs': [{k:x[k] for k in ['isolated','tau','charged_total','pure_bridge']} for x in witness['n6']['twocut_repairs']]},
 'Q_n7': {'source': witness['n7']['source'], 'target': witness['n7']['target'],
          'optimum': witness['n7']['original']['optimum_cuts'], 'failure': witness['n7']['failure']},
}
assert sum(Fraction(100,231) ** x for x in a['vector']) == Fraction(a['mass'])
assert sum(Fraction(100,231) ** x for x in b['B3']['vector']) == Fraction(b['B3']['mass'])
assert children['completed'] == reserved['completed'] == reserved['passed'] == 16
assert all(x['survival'] for x in children['rows'])
assert br['status'] == 'passed'
assert all(x['passed'] for x in pins + lean)
assert all(x['frozen_copy_matches'] for x in independent)

evidence_paths = [ROOT / 'research/rmaf/results' / ('algorithm-review-' + n + '.json') for n in data]
evidence_paths += [ROOT / row['path'] for row in pins]
evidence_paths += list(RESULTS.glob('algorithm-balanced-cover-verify-*.json'))
evidence_paths += [V / 'PRE-CANDIDATE-FREEZE.json', V / 'CONTROL-PIN.json', BV / 'INSTRUMENT-PIN.md', BV / 'instrument-freeze.sha256', Path(__file__)]
evidence_paths += list(V.glob('paid-*-input.json')) + list(V.glob('paid-*-stdout.json')) + list(V.glob('paid-*-stderr.log'))
evidence_paths += [V / p for p in ['independent_graph.py', 'independent_graph-pre-candidate-v1.py', 'review_macro.py', 'review_paid.py', 'review_each_reserved_child.py', 'compare_macro_delivery.py', 'run_controls.py', 'copy_mutations_and_arithmetic.py']]
evidence_paths += [BV / p for p in ['IndependentEdges.py', 'IndependentEdges.frozen-v1.txt', 'ReplayLean.py', 'ReplayLean.detector-v1.txt', 'ReplayWitnesses.py']]
evidence_paths += list((V / 'lean-isolated').glob('*.log')) + list((BV / 'lean-isolated').glob('*.log'))
evidence_paths += [RESULTS / p for p in ['algorithm-review-lean-replay-and-axioms.json', 'algorithm-review-original24-controls.json', 'algorithm-review-supplementary5-controls.json', 'algorithm-review-additional-controls.json', 'algorithm-review-paid-cli-controls.json', 'algorithm-review-macro-n7-rule7-control.json', 'algorithm-review-B2-smallness-through4.json', 'algorithm-review-exact-arithmetic.json']]
receipt = {'review_type': 'continuation of interrupted independent reviews; not another replication',
           'controls': controls, 'pin_checks': pins, 'independent_instrument': independent,
           'lean_audit': lean, 'balanced_final_receipt_status': br['status'],
           'old_balanced_detector_status': read('research/rmaf/results/algorithm-balanced-cover-verify-lean-detector-v1.json')['status'],
           'summary': summary,
           'evidence_hashes': {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(evidence_paths))},
           'all_hash_and_log_checks_passed': True,
           'scope': 'retained finite reproductions and kernel statements only; no new solver execution or universal closure'}
out = RESULTS / 'algorithm-review-continue-reconciliation-v4.json'
assert not out.exists()
out.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'pin_checks': len(pins), 'lean_rows': len(lean), 'all_passed': True,
                  'balanced_status': br['status'], 'summary': summary}, indent=2))
