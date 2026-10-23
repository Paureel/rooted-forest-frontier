#!/usr/bin/env python3
"""One-shot receipt extraction/replay for CB3's source-realized all-row failure."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import conflict_row_selector as selector
import conflict_solver as core
import conflict_dag_solver as dag

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
source_receipt = ROOT/'research/rmaf/results/algorithm-balanced-cover-continue-cb3-controls.json'
report = json.loads(source_receipt.read_text())
failures = [f for f in report['all_row_mass_failures'] if f['id'] == 'quotient-star']
assert failures and len({tuple(f['rows']) for f in failures}) == 1
fixture = next(f for f in json.loads((HERE/'CONTROLS-CB1.json').read_text())['ordinary']
               if f['id'] == 'quotient-star')
S, T = core.validate_input(fixture['source'], fixture['target'], 3)
H = tuple(core.conflicts(S, T))
closed, forced, steps = dag.forced_closure(core.minimal_rows(H))
assert forced == 0
chosen, all_rows = selector.choose_row(closed)
assert len(all_rows) == 26 and chosen['row'] == 960
assert chosen['mass'] == Fraction(9, 7)
assert all(sum(c['delta'] == 1 for c in p['kept']) >= 3 for p in all_rows)
assert all(p == selector.compile_row(closed, p['row']) for p in all_rows)

def clusters(tree):
    def visit(v):
        if not tree.children[v]:
            return frozenset(a for a, leaf in tree.leaf.items() if leaf == v), []
        parts = [visit(w) for w in tree.children[v]]
        leaves = frozenset().union(*(p[0] for p in parts))
        return leaves, [c for p in parts for c in p[1]] + [leaves]
    return set(visit(0)[1]) if tree.parent else set()

common = clusters(S) & clusters(T)
nontrivial = sorted([sorted(c) for c in common if 1 < len(c) < len(S.labels)])
assert nontrivial == []
result = {
    'kind': 'GLOBAL-CB3-ordinary-six-leaf-all-row-obstruction',
    'scope': 'exact finite source-derived obstruction to uniform one-row/forced-closure/residual-CNF-dominance recurrence; no nonexistence or general complexity lower bound',
    'source': fixture['source'], 'target': fixture['target'], 'budget': 3,
    'original_optimum': 3,
    'original_optimum_provenance': 'frozen quotient-star receipt, reproduced CB1/CB2/CB3 pinned control; source C1 remains separately scoped',
    'original_source_edges': S.edge_receipt((1 << len(S.edges)) - 1),
    'original_target_edges': T.edge_receipt((1 << len(T.edges)) - 1),
    'original_conflicts': [{'mask': h, 'causes': causes} for h, causes in core.conflicts(S,T).items()],
    'minimal_projected_conflicts': list(closed), 'forced_before_branch': list(core.bits(forced)),
    'all_row_count': len(all_rows), 'all_rows': selector.json_safe(all_rows),
    'best_row': selector.json_safe(chosen),
    'best_exact_mass_7_over_3': [9,7],
    'every_row_retains_at_least_three_unit_children': True,
    'uniform_cut_budget_base_strictly_below_three_possible': False,
    'blocked_algorithm_call': 'CB3 choose_row: supply a retained-child weighted mass <=1 before invoking the 7/3 recurrence',
    'reduced_eligibility': {'ordinary_distinct_equal_labels': True,
                            'added_rho': False,
                            'nontrivial_common_pendant_clades': nontrivial,
                            'common_cherry_reduced': True,
                            'stronger_reduction_history': 'not audited; no general reduced-model nonexistence inference'},
    'not_refuted': ['global amortization', 'multirow search macros', 'a different residual representation',
                    'partial guarded certificates into pure/triple terminal classes', 'safe-cover existence'],
    'source_receipt': str(source_receipt.relative_to(ROOT)),
    'source_receipt_sha256': hashlib.sha256(source_receipt.read_bytes()).hexdigest(),
    'hashes': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in [HERE/'SPEC-CB3.md', HERE/'conflict_row_selector.py',
                         HERE/'conflict_dag_solver.py', HERE/'conflict_solver.py', Path(__file__)]}
}
dest = ROOT/'research/rmaf/results/algorithm-balanced-cover-continue-cb3-obstruction.json'
dest.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'receipt': str(dest), 'rows': len(all_rows), 'best_row': 960,
                  'best_mass': [9,7], 'min_unit_children': 3,
                  'nontrivial_common_pendant_clades': nontrivial}))
