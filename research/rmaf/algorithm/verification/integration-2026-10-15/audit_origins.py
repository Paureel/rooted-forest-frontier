#!/usr/bin/env python3
"""Fresh module-origin inventory with preregistered audit-detector plants."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from replay_sources import compile_one

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BUILD = HERE / 'isolated'
OUT = ROOT / 'research/rmaf/results'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def audit_source(imports, modules):
    heads = '\n'.join(f'import all {name}' for name in imports)
    wanted = ', '.join(json.dumps(name) for name in modules)
    return heads + '\nimport Lean\nopen Lean Elab Command\n' + '''
run_cmd do
  let env ← getEnv
  let wanted : List String := [WANTED]
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!.toString
      if wanted.contains origin then
        let axs ← Lean.collectAxioms name
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        rows := rows.push <| Json.mkObj [
          ("name", toJson name.toString), ("origin", toJson origin),
          ("kind", toJson kind), ("axioms", toJson (axs.toList.map Name.toString))]
  logInfo m!"ORIGIN-AUDIT: {(Json.arr rows).compress}"
'''.replace('WANTED', wanted)

def run_audit(name, imports, origins):
    p = BUILD / f'{name}.lean'
    assert not p.exists()
    p.write_text(audit_source(imports, origins))
    result = compile_one(name)
    result['audit_origins'] = origins
    entries = []
    if result['passed']:
        raw = (ROOT / result['log']).read_text()
        marker = 'ORIGIN-AUDIT: '
        assert raw.count(marker) == 1
        entries, _ = json.JSONDecoder().raw_decode(raw.split(marker, 1)[1].lstrip())
        entries.sort(key=lambda r: (r['origin'], r['name']))
        assert entries and set(r['origin'] for r in entries) == set(origins)
    return result, entries

def main():
    base = json.loads((OUT / 'algorithm-integration-fresh-review-source-replay-v1.json').read_text())
    assert base['all_passed']
    kernel = json.loads((HERE / 'KERNEL-CONTROL-PIN.json').read_text())
    names = ['KernelClean', 'KernelCustomPlant', 'KernelExplicitFalse', 'KernelBrokenImport']
    rows = []
    for name, plant in zip(names, kernel['plants']):
        source = BUILD / f'{name}.lean'
        assert not source.exists()
        source.write_text(plant['source'])
        expected = plant['expected_compile_exit']
        row = compile_one(name, expected=expected)
        output = (ROOT / row['log']).read_text()
        row['plant_id'] = plant['id']
        row['explicit_false_diagnostics'] = output.count('is false')
        if name == 'KernelExplicitFalse':
            row['passed'] &= row['explicit_false_diagnostics'] == 1 and 'Tactic `decide` proved' in output
        elif name == 'KernelBrokenImport':
            row['passed'] &= row['explicit_false_diagnostics'] == 0 and 'DefinitelyMissingIntegrationReviewModule' in output
        rows.append(row)
        assert row['passed'], row
    clean_row, clean = run_audit('KernelCleanAudit', ['KernelClean'], ['KernelClean'])
    custom_row, custom = run_audit('KernelCustomAudit', ['KernelCustomPlant'], ['KernelCustomPlant'])
    allowed = set(kernel['allowed_axioms'])
    clean_bad = [r for r in clean if not set(r['axioms']) <= allowed or r['kind'] == 'axiom']
    custom_bad = [r for r in custom if not set(r['axioms']) <= allowed or r['kind'] == 'axiom']
    assert clean_row['passed'] and custom_row['passed'] and not clean_bad
    assert any(r['name'] == 'AuditPlant.hiddenBad' and r['kind'] == 'axiom' for r in custom_bad)
    assert any('_private.' in r['name'] and 'privateLeak' in r['name'] and 'AuditPlant.hiddenBad' in r['axioms'] for r in custom_bad)
    assert any(r['name'] == 'AuditPlant.leak' and 'AuditPlant.hiddenBad' in r['axioms'] for r in custom_bad)
    modules = sorted(json.loads((HERE / 'CANDIDATE-PIN.json').read_text())['isolated_source_modules'])
    modules.remove('FalseControls')
    audit_row, entries = run_audit('CandidateOriginAudit', modules, modules)
    assert audit_row['passed']
    assert len({r['name'] for r in entries}) == len(entries)
    bad = [r for r in entries if not set(r['axioms']) <= allowed or r['kind'] == 'axiom']
    author_path = ROOT / 'research/rmaf/algorithm/universal233/integration/replay/20261015T072236Z/certificate.json'
    author = json.loads(author_path.read_text())
    index = {r['name']: r for r in entries}
    comparisons = [{'name': n, 'found': n in index,
                    'axioms_match': n in index and sorted(index[n]['axioms']) == sorted(ax)}
                   for n, ax in author['axioms'].items()]
    assert len(comparisons) == 449 and all(r['found'] and r['axioms_match'] for r in comparisons)
    inventory = {'created_utc': datetime.now(timezone.utc).isoformat(),
                 'enumeration': 'Lean Environment imported-module origin, import all visibility; every constant kind, including private/generated',
                 'candidate_modules': modules, 'total_originating_declarations': len(entries),
                 'per_module': {m: sum(r['origin'] == m for r in entries) for m in modules},
                 'private_declarations': [r['name'] for r in entries if '_private.' in r['name']],
                 'additional_to_author_explicit_inventory': [r['name'] for r in entries if r['name'] not in author['axioms']],
                 'allowed_axioms': sorted(allowed), 'violations': bad, 'entries': entries,
                 'author449_comparison': comparisons, 'audit_compile': audit_row,
                 'source_sha256': sha(Path(__file__)), 'author_audit_reused': False}
    (HERE / 'AXIOM-INVENTORY.json').write_text(json.dumps(inventory, indent=2) + '\n')
    receipt = {'created_utc': datetime.now(timezone.utc).isoformat(), 'all_passed': not bad,
               'kernel_plant_rows': rows, 'clean_audit': clean_row, 'custom_audit': custom_row,
               'clean_entries': clean, 'rejected_custom_entries': custom_bad,
               'candidate_origin_declarations': len(entries), 'candidate_origin_modules': len(modules),
               'candidate_audit': audit_row, 'custom_axiom_private_control_caught': True,
               'generic_import_refusal_not_counted_as_falsity': True,
               'author449_all_matched': True, 'inventory_sha256': sha(HERE / 'AXIOM-INVENTORY.json'),
               'source_sha256': sha(Path(__file__)), 'kernel_control_pin_sha256': sha(HERE / 'KERNEL-CONTROL-PIN.json')}
    (OUT / 'algorithm-integration-fresh-review-origin-audit-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ['all_passed', 'candidate_origin_declarations', 'candidate_origin_modules', 'custom_axiom_private_control_caught', 'author449_all_matched']}))
    raise SystemExit(0 if not bad else 1)

if __name__ == '__main__': main()
