#!/usr/bin/env python3
"""One-shot exact-path pre-candidate control/source freeze; no candidate reads."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

sources = {
    'research/rmaf/algorithm/TARGET.md': 'read all 42 lines; target/status :5–13',
    'research/rmaf/algorithm/universal233/core/CoreGraph.lean': 'read all 268 lines; adjacency :23–30, support structure :189–195, singleton alternatives :228–258',
    'research/rmaf/algorithm/universal233/core/CoreProgram.lean': 'read all 317 lines; original origins/normalization/erase :21–46, choose :60–74, attempt guards :97–106, finite budget :118–126',
    'research/rmaf/lean/RMAF.lean': 'read all 393 lines; proper instance :17–24, restriction :83–91, spans :114–133, Boolean agreement :149–157',
}
copies = HERE / 'frozen-inputs'
copies.mkdir(exist_ok=False)
contact_rows = []
for name, locators in sources.items():
    source = ROOT / name
    dest = copies / source.name
    dest.write_bytes(source.read_bytes())
    contact_rows.append({'path': name, 'read_locator': locators,
                         'sha256': sha(source), 'frozen_copy': str(dest.relative_to(ROOT)),
                         'copy_sha256': sha(dest), 'role': 'contacted specification/dependency'})
contacts = {
    'lineage': 'same independent reviewer; zero additional replications',
    'prior_contacts': 'earlier frozen and geometry review knowledge/graph instruments, shared original RMAF model',
    'new_mathematical_records_read': contact_rows,
    'metadata_only_exposure': 'filename-only initial rg over permitted basenames under research/rmaf exposed integration/replay path names; no candidate/replay/result/FIRST-GAP content opened; immediately reported and exact paths used thereafter',
    'coordinator_disposition': 'metadata contact, not mathematical candidate inspection; continue controls without permission gate',
    'new_instrument': 'original_graph.py, explicit graph terminal pruning, bottom-up signatures, flat current-state updates; no old checker or candidate/prover imports',
    'shared_mathematical_layer': 'ordinary rooted tree/partition semantics and the explicitly contacted core dependency definitions; not an extra replication',
}
(HERE / 'SOURCE-CONTACTS.json').write_text(json.dumps(contacts, indent=2) + '\n')
controls = json.loads((HERE / 'CONTROL-PIN.json').read_text())
assert controls['count'] == len(controls['controls']) == 49
files = [ROOT / name for name in sources]
files += [HERE / x for x in ['SPEC-PIN.md', 'CONTROL-PIN.json', 'define_controls.py',
                             'original_graph.py', 'SOURCE-CONTACTS.json', 'freeze.py']]
files += list(copies.iterdir())
freeze = {
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'phase': 'pre-candidate, before first checker execution',
    'scope': 'finite instrument/control readiness only; no scientific integration acceptance',
    'declared_controls': 49, 'declared_false_expectations': 49,
    'exact_comparison': 'whole returned JSON-value equality; each false expected twin must compare unequal',
    'timing_plan': 'pilot first3 literal controls, size-pilot6 graph controls, measured row upper bound times49 before full fixed battery; no census',
    'candidate_content_inspected': False,
    'candidate_path_metadata_exposed': True,
    'additional_independent_replications': 0,
    'all_main_milestones': {'complete_algorithm': 'OPEN', 'universal_correctness': 'OPEN', 'smaller_base': 'OPEN'},
    'files_sha256': {str(p.relative_to(ROOT)): sha(p) for p in files},
}
dest = HERE / 'PRE-CANDIDATE-FREEZE.json'
assert not dest.exists()
dest.write_text(json.dumps(freeze, indent=2) + '\n')
print(json.dumps({'freeze_sha256': sha(dest), 'files_pinned': len(files),
                  'declared_controls': 49, 'checker_executed': False}))
