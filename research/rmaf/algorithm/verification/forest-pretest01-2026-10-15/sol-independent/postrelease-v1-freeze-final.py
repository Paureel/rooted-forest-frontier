#!/usr/bin/env python3
"""One-shot immutable local-review verdict and complete evidence inventory."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import time

HERE=Path(__file__).resolve().parent
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p):return {'path':str(p.relative_to(ROOT)),'sha256':digest(p),'bytes':p.stat().st_size}

start=time.perf_counter()
ready=HERE/'READY-v1.json'
release=HERE.parent/'ROOT-RELEASE-v1.json'
assert digest(ready)=='040188f56c73ddb0353b0033411a673f7784acaf36c2d39f549f88fe79c596f4'
assert digest(release)=='646206345de86873e0937653e1cc9349c43d456d34001cd85617d60158d22e6f'
frozen=json.loads(ready.read_text())
for key in ('licensed_inputs','own_artifacts'):
    for record in frozen[key]:assert digest(ROOT/record['path'])==record['sha256'],record['path']
for package in json.loads((HERE/'postrelease-v1-package-pins.json').read_text()):
    assert digest(ROOT/package['manifest'])==package['sha256']
    for record in package['members']:assert digest(ROOT/record['path'])==record['sha256'],record['path']

semantics=json.loads((HERE/'postrelease-v1-semantics-full-v2.json').read_text())
origins=json.loads((HERE/'postrelease-v1-origin-analysis-v3.json').read_text())
bodies=json.loads((HERE/'postrelease-v1-body-completeness.json').read_text())
references=json.loads((HERE/'postrelease-v1-reference-ruling.json').read_text())
regression=json.loads((HERE/'postrelease-v1-regression-controls.json').read_text())
assert semantics['status']=='PASS' and bodies['status']=='PASS' and regression['status']=='PASS'
assert origins['status']=='PASS_QUALIFIED_PROOF_ORIGINS' and references['status']=='PASS_QUALIFIED_LIBRARY_TRUST'
compressed=sum(p.stat().st_size for p in HERE.rglob('*.gz'))
assert compressed<=256*2**20 and shutil.disk_usage(HERE).free>=3*2**30
verdict={'status':'COMPLETE_QUALIFIED_LOCAL_REVIEW_NOT_GLOBAL_ACCEPTANCE',
         'semantic_interface_count':'CONFIRMED_WITH_STATED_TRUST_AND_CONTACT_QUALIFICATIONS',
         'producer_origin':'QUALIFIED_THREE_EQUAL_TYPE_GENERATED_PROOF_BODY_ORIGIN_MISMATCHES',
         'scope':'full-current-forest cost0/1 named main-dispatcher pretest only',
         'fresh_scientific_modules':origins['modules'],'raw_producer_occurrences':origins['raw_occurrences'],
         'distinct_producer_names':origins['distinct_names'],'project_axiom_producers':origins['axioms'],
         'ordinary_bodies':bodies['recorded_ordinary_bodies'],'recursor_rule_rhs':bodies['recursor_rule_rhs_recorded'],
         'private_producers':origins['private_producers'],'generated_partial_helpers':len(origins['truly_unsafe_or_partial']),
         'reference_count':references['references_resolved'],'trusted_Init_references':references['external_references'],
         'frozen_fixture_cases':len(semantics['rows']),'full_predicate_checks':semantics['partition_checks'],
         'direct_candidate_API_entries':semantics['candidate_entries'],
         'origin_qualifications':origins['merge_origin_qualifications'],
         'summary_contact':'incidental team inventory after graph expectations/runs; no pristine-summary-contact credit',
         'postcontact_repairs':['malformed-domain comparator','lossless Syntax metadata extension',
                                'explicit proof-origin qualification','projection-reference extraction from retained DAG'],
         'open':['parent dispatcher integration and LocalIH/current-budget binding','global original-source cut recovery',
                 'tight formal source instruction bound','compiled IR/runtime equivalence','full Algorithm',
                 'full Correctness','Smaller-base','novelty','VERIFIED-CLOSED','publication acceptance'],
         'compressed_output_bytes_including_failed_partial':compressed,'minimum_free_space_bytes':3*2**30,
         'report':'postrelease-v1-REPORT.md','source_work':'postrelease-v1-SOURCE-WORK.md',
         'contact_failure_ledger':'postrelease-v1-CONTACT.md'}
verdict_path=HERE/'postrelease-v1-VERDICT.json';assert not verdict_path.exists()
verdict_path.write_text(json.dumps(verdict,indent=2)+'\n')

manifest=HERE/'postrelease-v1-FINAL-MANIFEST.json';assert not manifest.exists()
files=sorted(p for p in HERE.rglob('*') if p.is_file())
result={'status':'IMMUTABLE_COMPLETE_QUALIFIED_LOCAL_REVIEW',
        'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'ready':pin(ready),'release':pin(release),
        'report':pin(HERE/'postrelease-v1-REPORT.md'),'verdict':pin(verdict_path),
        'scientific_closure':'postrelease-v1-build-full.json','own_files':[pin(p) for p in files],
        'all_original_READY_pins_unchanged':True,'all_released_package_pins_rechecked':1094,
        'compressed_output_bytes_including_failed_partial':compressed,'disk_free_bytes':shutil.disk_usage(HERE).free,
        'global_milestones':'ALL OPEN','no_new_blind_replication_credit_for_repairs_or_repeated_controls':True,
        'freeze_seconds':time.perf_counter()-start}
manifest.write_text(json.dumps(result,indent=2)+'\n')
for p in (manifest,HERE/'postrelease-v1-REPORT.md',verdict_path):os.chmod(p,0o444)
print(json.dumps({'manifest':str(manifest),'sha256':digest(manifest),'own_files':len(files),
                  'compressed_bytes':compressed,'free_bytes':result['disk_free_bytes'],'seconds':result['freeze_seconds']}))
