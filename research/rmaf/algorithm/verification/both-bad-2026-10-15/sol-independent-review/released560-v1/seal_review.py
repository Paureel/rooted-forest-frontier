#!/usr/bin/env python3
"""One-shot final review inventory. Streaming hashes preserve bounded memory."""
import hashlib,json,pathlib,time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def load(p):return json.loads(p.read_text())
def save(name,d):(HERE/name).write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')

def main():
    assert not (HERE/'FINAL-v1.json').exists(),'never replace a sealed final receipt'
    ready=HERE.parent/'READY-v1.json'
    assert sha(ready)=='d49dbb5600a0d0720e401a63b8a3efb085aa10700c3a02d5dd5922dfab66b25c'
    original=load(ready)
    for r in original['files']:assert sha(ready.parent/r['path'])==r['sha256'],r['path']
    manifest=ROOT/'research/rmaf/algorithm/universal233/both_bad/BOTH-BAD-MANIFEST-v1.json'
    assert sha(manifest)=='da001ef62039c916cf6db24f61c994094b5b1750f5be9130ddaf512ae5fbe20d'
    author=load(manifest)
    for r in author['immutable_files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
    comparison=load(HERE/'COMPILED-CONTROL-COMPARISON-v1.json')
    provenance=load(HERE/'PROVENANCE-CHECKS-v1.json')
    assert comparison['execution_comparisons']==305 and comparison['mass_comparisons']==915
    assert len(comparison['frozen_callback_mismatches'])==4
    assert provenance['stored_occurrences']==4675 and provenance['direct_scientific_axioms']==0
    assert load(HERE/'AXIOM-INVENTORY-SCOPE-v2.json')['author_manifest_axiom_summary']==provenance['dependency_axioms']
    contacts={
      'root_release':{'path':'research/rmaf/algorithm/verification/both-bad-2026-10-15/ROOT-RELEASE-v1.json',
        'sha256':sha(ROOT/'research/rmaf/algorithm/verification/both-bad-2026-10-15/ROOT-RELEASE-v1.json')},
      'candidate_scope':'Only exact560 manifest files were read/copied; earlier source_inputs paths remained metadata and were not opened.',
      'post_release_source_contacts':load(HERE/'SOURCE-MAP-v1.json')['copied_sources'],
      'semantic_full_reads':['BothProgram','Planner','Dispatcher','ForestContract','PlanCover','Crossing','CoreCover',
        'FourProbe','PlannerSources','MafCaller','ExecutionFacts','PlannerGeometry','RetainedLower','RetainedBridge',
        'CheapPlannerCover','OrdinaryBridge','PlanActualMass','CallDecrease','ExecutionWork','PlannerWork',
        'QueryCaller','QueryWork','CheapPlanMass','ActualBadSlots','QueryTrace','FullTransport','Equivalence',
        'ResidualConsumer','SelectedContinuation'],
      'other_sources':'All160 sources parsed for imports, pinned and kernel-rebuilt; source proofs not in semantic_full_reads are not claimed natural-language full reads.',
      'author_control_contact':'Author control modules present in the released dependency closure compiled only after release. Independent expected values remain the original READY values.',
      'other_reviewer_implementation_contact':False,'author_or_other_reviewer_communication':False,
      'own_reuse':'Precontact graph instruments, ProducerAudit and toy_runner/producer_runner utilities only; explicit adapters recorded.',
      'additional_skill':'prose-lint fully read; report self-passes retained; independent fresh framing remains separate.'}
    save('POSTRELEASE-CONTACTS-v1.json',contacts)
    failures={
      'precontact':'See unchanged READY RETAINED-FAILURES-v1.json and PREPARATION.md.',
      'S11_q4':'One frozen entry-to-call reference error reproduced under4 oracle variants; original expected value unchanged, post-contact erratum separate.',
      'stream_parser_v1':'First line-layout parser failed frozen toy and pilot; generic tokenizer passed plants before full use. Both logs and failed source retained.',
      'axiom_summary_note':'A sliced metadata display was misread as a complete list. Full lists agree; erroneous v1 explanatory note preserved and superseded by v2.',
      'compiler_warning':'CompiledControls emits an unused-variable warning; adapter parser requires exactly one complete JSON payload.',
      'source_build_or_math_failures':[]}
    save('POSTRELEASE-FAILURES-v1.json',failures)
    verdict={
      'semantic':'CONFIRMED_LOCAL_CONDITIONAL_MATH',
      'consumer':'CONFIRMED_WITH_EXPLICIT_ACTUAL_CALLBACK_EXACTNESS_IH',
      'actual_control':'CONFIRMED_FINITE_WITH_PRESERVED_FROZEN_q4_REFERENCE_ERROR',
      'work_model':'BILLING_ALGEBRA_CONFIRMED_CALLER_OPERATION_CORRESPONDENCE_OPEN',
      'provenance':'STORED_PRODUCER_KERNEL_SCOPE_CONFIRMED_COMPILER_AUXILIARY_BODIES_EXCLUDED'}
    summary={
      'status':'SCOPED_CONDITIONAL_PACKAGE_REVIEW_COMPLETE_RUNTIME_BRIDGE_OPEN',
      'verdicts':verdict,'ready_files_unchanged':115,'author_files_unchanged':560,
      'scientific_modules_cold_built':160,'scientific_oleans_copied':0,
      'finite_original_refiners_precontact':13650,'compiled_core_receipt_comparisons':120,
      'compiled_plan_comparisons':100,'compiled_executions':305,'actual_callback_occurrences':378,
      'independent_original_return_checks':79,'exact_rational_mass_comparisons':915,
      'stored_scientific_occurrences':4675,'resolved_scientific_names':4647,
      'direct_custom_axioms':0,'allowed_dependency_axioms':provenance['dependency_axioms'],
      'private_occurrences':418,'generated_recursors':64,'compiler_auxiliary_names_inventory_only':1418,
      'all_global_milestones':'OPEN','complete_ordinary_solver':False,'global_runtime_or_base':False,
      'novelty_or_independent_statistical_replication':False,'VERIFIED_CLOSED':False,
      'future_fresh_context_framing':'Separately assigned, not provided by this arm.',
      'report':'VERDICT-v1.md','consumer_trace':'CONSUMER-TRACE-v1.md',
      'raw_map_archives':'RAW-MAP-ARCHIVES-v1.json','contacts':'POSTRELEASE-CONTACTS-v1.json',
      'failures':'POSTRELEASE-FAILURES-v1.json'}
    save('SUMMARY-v1.json',summary)
    rows=[];excluded=[]
    for p in sorted(HERE.rglob('*')):
        if not p.is_file():continue
        rel=str(p.relative_to(HERE))
        if '__pycache__' in p.parts or p.suffix=='.pyc':excluded.append(rel);continue
        if rel in ['FINAL-v1.json','FINAL-v1.sha256']:continue
        rows.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p)})
    final={'status':summary['status'],'created_unix':time.time(),'summary':summary,
      'READY_sha256':sha(ready),'author_manifest_sha256':sha(manifest),
      'files':rows,'transient_exclusions':excluded,'future_changes':'New separately named receipts only; do not edit sealed files.'}
    save('FINAL-v1.json',final);digest=sha(HERE/'FINAL-v1.json')
    (HERE/'FINAL-v1.sha256').write_text(digest+'  FINAL-v1.json\n')
    for r in rows:
        p=HERE/r['path'];p.chmod(p.stat().st_mode&~0o222)
    for name in ['FINAL-v1.json','FINAL-v1.sha256']:
        p=HERE/name;p.chmod(p.stat().st_mode&~0o222)
    print(json.dumps({'status':summary['status'],'files':len(rows),'FINAL_sha256':digest,
      'SUMMARY_sha256':sha(HERE/'SUMMARY-v1.json'),'VERDICT_sha256':sha(HERE/'VERDICT-v1.md')}))

if __name__=='__main__':main()
