#!/usr/bin/env python3
"""One-shot state-reduction replay adapted from completed restriction_bridge/replay.py.

Rebuilds only original RMAF, three completed literal restriction modules with
pinned import-name adaptations, and this arm's local sources. Author kernel
replay is separate from fresh nonauthor acceptance. Failures remain on disk.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = HERE.parent
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT = ROOT / 'results' / ('algorithm-universal233-state-' + STAMP)
OUT.mkdir(parents=True, exist_ok=False)
(HERE / 'LATEST-REPLAY.txt').write_text(str(OUT) + '\n')
SPECS = [('RMAF', ROOT / 'research/rmaf/lean/RMAF.lean', None)]
SPECS += [(new, BASE / 'restriction_bridge' / (old + '.lean'), adaptation)
          for new, old, adaptation in [
              ('StateRestriction', 'Restriction', None),
              ('StateEmbedding', 'Embedding', ('import Restriction', 'import StateRestriction')),
              ('StatePartition', 'Partition', ('import Embedding', 'import StateEmbedding'))]]
SPECS += [(n, HERE / (n + '.lean'), None) for n in [
    'State', 'Controls', 'Singleton', 'Removal', 'Forward', 'LeafClear', 'Reverse',
    'CherryGraph', 'CherryTopology', 'Consumers']]
MODS = [n for n, _, _ in SPECS]
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
ENV = dict(os.environ, LEAN_PATH=str(OUT))
record = dict(status='RUNNING', grade='AUTHOR_KERNEL_REPLAY_ONLY',
              singleton_cleanup='PENDING', common_cherry='OPEN',
              all_three_main_milestones='OPEN', fresh_nonauthor_acceptance=False,
              builds=[], controls={}, input_hashes={}, adaptations=[],
              first_unproved_graph_consumer='EndpointReassignmentEmbeddings in OPEN-CONSUMER-v1.md')

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save():
    (OUT / 'certificate.json').write_text(json.dumps(record, indent=2) + '\n')

def clean(s):
    s = re.sub(r'/\-.*?\-/', lambda m: '\n' * m.group().count('\n'), s, flags=re.S)
    return re.sub(r'--[^\n]*', '', s)

def run(n, build=False):
    args = [str(ROOT / 'bootloops-lean')]
    if build:
        args += ['-o', str(OUT / (n + '.olean'))]
    args += [str(OUT / (n + '.lean'))]
    start = time.monotonic()
    p = subprocess.run(args, cwd=OUT, env=ENV, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=60)
    (OUT / (n + '.log')).write_text(p.stdout)
    record['builds'].append(dict(module=n, returncode=p.returncode,
                                seconds=round(time.monotonic() - start, 6)))
    save()
    return p

# Pin permitted completed source lineage, then record every import adaptation.
restriction_receipt = BASE / 'restriction_bridge/replay/20261015T090816Z/certificate.json'
prior = json.loads(restriction_receipt.read_text())
record['restriction_dependency_receipt_sha256'] = digest(restriction_receipt)
for n, path, adaptation in SPECS:
    if n in ['RMAF', 'StateRestriction', 'StateEmbedding', 'StatePartition']:
        rel = str(path.relative_to(ROOT))
        assert digest(path) == prior['input_hashes'][rel], 'completed dependency changed: ' + rel
    src = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', clean(src)), str(path)
    if adaptation:
        old, new = adaptation
        assert src.count(old) == 1
        src = src.replace(old, new, 1)
        record['adaptations'].append(dict(module=n, source=str(path.relative_to(ROOT)),
                                         old=old, new=new, adapted_sha256=hashlib.sha256(src.encode()).hexdigest()))
    (OUT / (n + '.lean')).write_text(src)
    record['input_hashes'][str(path.relative_to(ROOT))] = digest(path)
for path in [HERE / 'TARGET-v1.md', HERE / 'CONTROLS-v1.md', HERE / 'CONTROLS-PIN-v1.json',
             HERE / 'FalseControls.lean', HERE / 'OPEN-CONSUMER-v1.md', Path(__file__),
             ROOT / 'bootloops-lean', ROOT / 'bootloops-lake', ROOT / 'bootloops-python']:
    record['input_hashes'][str(path.relative_to(ROOT))] = digest(path)
for name in ['FalseControls.lean', 'TARGET-v1.md', 'CONTROLS-v1.md', 'CONTROLS-PIN-v1.json',
             'OPEN-CONSUMER-v1.md']:
    (OUT / name).write_bytes((HERE / name).read_bytes())
(OUT / 'preproof-controls-receipt.json').write_bytes((HERE / 'build/preproof-controls-receipt.json').read_bytes())
(OUT / 'lean-toolchain').write_bytes((BASE / 'integration/lean-toolchain').read_bytes())
for wrapper in ['bootloops-lean', 'bootloops-lake']:
    p = subprocess.run([str(ROOT / wrapper), '--version'], cwd=OUT, env=ENV, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
    (OUT / (wrapper + '-version.log')).write_text(p.stdout)
    assert p.returncode == 0
    record[wrapper + '_version'] = p.stdout.strip()

(OUT / 'TrueControl.lean').write_text('import Std\nexample : (2 : Nat) + 3 = 5 := by decide\n')
(OUT / 'FalseControl.lean').write_text('import Std\nexample : (2 : Nat) + 3 = 6 := by decide\n')
assert run('TrueControl').returncode == 0
p = run('FalseControl')
assert p.returncode != 0 and 'is false' in p.stdout
record['controls'].update(known_true='ACCEPTED', known_false='REJECTED')
for n, _, _ in SPECS:
    p = run(n, True)
    assert p.returncode == 0 and not re.search(r'error:|sorryAx|declaration uses .sorry.', p.stdout), (n, p.stdout)
    if n == 'Controls':
        p = run('FalseControls')
        assert p.returncode != 0 and p.stdout.count('is false') == 4, p.stdout
        record['controls']['four_pinned_false_claims'] = 'REJECTED_4_OF_4'

inventory = '''import Consumers
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [MODULES]
  for mod in env.header.moduleNames do
    let path ← liftIO <| findOLean mod
    logInfo m!"PATH|{mod}|{path}"
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''.replace('MODULES', ', '.join('`' + n for n in MODS))
(OUT / 'ModuleInventory.lean').write_text(inventory)
p = run('ModuleInventory')
assert p.returncode == 0, p.stdout

def parse(s):
    origins = re.findall(r'^MODULE\|([^|]+)\|(.+)$', s, re.M)
    axioms = re.findall(r'^MODAUDIT\|([^|]+)\|([^\n]*)$', s, re.M)
    assert origins and len(origins) == len(axioms) == len(set(origins)), 'incomplete/duplicate audit'
    assert {n for _, n in origins} == {n for n, _ in axioms}, 'missing axiom declaration'
    assert {m for m, _ in origins} == set(MODS), 'missing/extra source module'
    paths = dict(re.findall(r'^PATH\|([^|]+)\|(.+)$', s, re.M))
    for mod, rawpath in paths.items():
        path = Path(rawpath).resolve()
        if mod in MODS:
            assert path == OUT / (mod + '.olean'), 'wrong local module origin: ' + mod
        else:
            assert path.is_relative_to(ROOT / '.runtime/elan/toolchains'), 'non-toolchain dependency: ' + str(path)
    for mod in MODS:
        assert mod in paths, 'missing source path: ' + mod
    return origins, axioms, paths

origins, axioms, paths = parse(p.stdout)
for label, corrupted in [
    ('missing_axiom_record', re.sub(r'^MODAUDIT\|[^\n]+\n', '', p.stdout, count=1, flags=re.M)),
    ('wrong_module_path', re.sub(r'^PATH\|StateRestriction\|[^\n]+', 'PATH|StateRestriction|/tmp/foreign.olean', p.stdout, flags=re.M)),
    ('wrong_module_origin', re.sub(r'^MODULE\|StateRestriction\|', 'MODULE|ForeignModule|', p.stdout, count=1, flags=re.M)),
]:
    try:
        parse(corrupted)
    except AssertionError as err:
        record['controls'][label] = 'CAUGHT: ' + str(err)
    else:
        raise AssertionError('corruption survived: ' + label)
record['module_origin_counts'] = {n: sum(mod == n for mod, _ in origins) for n in MODS}
record['module_origin_total'] = len(origins)
record['resolved_module_paths'] = paths
record['axiom_union_observed'] = sorted({x.strip() for _, xs in axioms for x in xs.split(',') if x.strip()})
assert set(record['axiom_union_observed']) <= ALLOWED
(OUT / 'PlantModel.lean').write_text('namespace HiddenStatePlant\naxiom borrowed : False\nend HiddenStatePlant\n')
assert run('PlantModel', True).returncode == 0
(OUT / 'ModulePlantAudit.lean').write_text('import PlantModel\n' + inventory.replace('`Consumers]', '`Consumers, `PlantModel]'))
p = run('ModulePlantAudit')
assert p.returncode != 0 and 'REJECT_CUSTOM_AXIOM|HiddenStatePlant.borrowed|HiddenStatePlant.borrowed' in p.stdout
record['controls']['hidden_custom_axiom'] = 'CAUGHT'
corrupt_source = OUT / 'State-corrupted.txt'
corrupt_source.write_bytes((OUT / 'State.lean').read_bytes() + b'\n-- deliberate source corruption\n')
assert digest(corrupt_source) != record['input_hashes'][str((HERE / 'State.lean').relative_to(ROOT))]
record['controls']['source_byte_corruption'] = 'CAUGHT'
for rel, sha in record['input_hashes'].items():
    assert digest(ROOT / rel) == sha, 'source changed during replay: ' + rel
for n, path, adaptation in SPECS:
    src = path.read_text()
    if adaptation:
        src = src.replace(*adaptation, 1)
    assert (OUT / (n + '.lean')).read_text() == src, 'snapshot changed: ' + n
record.update(status='PASS_AUTHOR_KERNEL_REPLAY_PARTIAL_TARGET', singleton_cleanup='CLOSED_UNVERIFIED',
              cherry_separation='CLOSED_UNVERIFIED', cherry_endpoint_topology='CLOSED_UNVERIFIED',
              common_cherry='OPEN', source_priority='OPEN', full_algorithm='OPEN', runtime='OPEN')
record['module_inventory_sha256'] = digest(OUT / 'ModuleInventory.log')
save()
summary = {k: record[k] for k in ['status', 'grade', 'singleton_cleanup', 'common_cherry',
    'cherry_separation', 'cherry_endpoint_topology', 'module_origin_total', 'module_origin_counts',
    'axiom_union_observed', 'controls', 'all_three_main_milestones', 'fresh_nonauthor_acceptance',
    'first_unproved_graph_consumer']}
summary['receipt'] = str(OUT.relative_to(ROOT))
(ROOT / 'research/rmaf/results' / ('algorithm-universal233-state-' + STAMP + '.json')).write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
