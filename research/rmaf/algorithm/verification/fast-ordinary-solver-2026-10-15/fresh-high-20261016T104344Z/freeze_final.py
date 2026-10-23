#!/usr/bin/env python3
"""One-shot freeze of this worker's disjoint directory; no upstream mutations."""
import datetime, hashlib, json, pathlib
here=pathlib.Path(__file__).resolve().parent
outpath=here/'FINAL-MANIFEST-v1.json'
if outpath.exists(): raise SystemExit('REFUSED existing final manifest')
validation=json.loads((here/'FINAL-VALIDATION-v2.json').read_text())
assert validation['formal_component_checks_passed'] and validation['body_archive_replay_passed']
files=[]
for path in sorted(here.iterdir()):
    if path.is_file():
        h=hashlib.sha256()
        with path.open('rb') as source:
            for block in iter(lambda:source.read(4*1024**2),b''): h.update(block)
        files.append(dict(path=path.name,bytes=path.stat().st_size,sha256=h.hexdigest()))
out=dict(version=1,at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         status='OPEN_SOURCE_BOUNDARY_AND_RESOURCE_POLICY',no_further_writes=True,
         directory=str(here),target_sha256='605fb29536ffc21c437f39616728501b69e91d4f765e612c75bfb823c63d4939',
         full_literal_theorem_proved=False,counterexample_obtained=False,
         proved_components=['OwnHigh.cherry_distinct','OwnHigh.agreement_singleton_or_shared',
                            'OwnHigh.agreement_source_cherry','OwnHigh.refines_of_no_crossing'],
         exact_conditional_consumer='OwnHigh.literal_consumer',
         unproved_premise='OwnHigh.SourceBoundaryObligation',
         remaining_actual_consumer='Actual HighRule use-site and full coverage not inspected; separate interface review required.',
         dependency_graph='DEPENDENCY-GRAPH-v2.json',body_archive='BODY-ARCHIVE-v3.json',
         axioms=['Quot.sound','propext','Classical.choice'],forbidden_reached=[],unknown_dependency_status=[],
         primitive_reuse='Program definitions, generated equation facts, RestrictionBridge.root_not_prepend and its generated wrapper; zero independent credit for reused facts.',
         resource_policy_acceptance=False,independent_final_acceptance=False,
         no_fullsolver_runtime_base_native_novelty_replication_acceptance=True,
         evidence_files=files)
outpath.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(path=str(outpath),sha256=hashlib.sha256(outpath.read_bytes()).hexdigest(),
                     files=len(files),status=out['status'],no_further_writes=True)))
