"""Post-inspection semantic witness: LCA-closed does not imply connected.

One-shot scope check, not a counterexample to any asserted Lean theorem.
Frozen expected answer below before this script's first execution.
"""
import json
from pathlib import Path
from partition_oracle import Tree

region = {(), (0, 0)}
expected_lca_closed = True
expected_connected = False
lca_closed = all(Tree.meet(a, b) in region for a in region for b in region)
seen = {()}
while True:
    extra = {v for v in region if any(v[:-1] == u or u[:-1] == v for u in seen if u != v)}
    if extra <= seen:
        break
    seen |= extra
connected = seen == region
assert lca_closed is expected_lca_closed
assert connected is expected_connected
receipt = {'kind':'semantic-scope-witness','region':[list(x) for x in sorted(region)],
           'lca_closed':lca_closed,'connected':connected,'missing_path_vertex':[0],
           'claim':'LCA closure alone is weaker than graph connectedness',
           'not_a_counterexample_to_Lean_theorem':True,
           'provenance':'post-inspection auxiliary scope witness; not part of held-out solver campaign'}
output = Path(__file__).resolve().parents[2] / 'results/triple-dp-verification-lca-gap.json'
if output.exists():
    raise FileExistsError('preserve prior receipt: ' + str(output))
output.write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
