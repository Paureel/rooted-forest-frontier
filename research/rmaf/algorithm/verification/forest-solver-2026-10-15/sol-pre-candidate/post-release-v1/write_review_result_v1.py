#!/usr/bin/env python3
"""Assemble the scoped review result from retained exact receipts."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
def read(name):return json.loads((HERE/name).read_text())
source=read('source-rebuild-v1.json');origins=read('candidate-origin-batches-v2.json')
actual=read('actual-check-full-v3.json');names=read('adapter-name-classification-v1.json')
natural=read('natural-name-classification-v1.json');scope=read('PROVENANCE-SCOPE-CHECK-v1.json')
ir=read('KERNEL-IR-SCOPE-v1.json');signature=read('SIGNATURES-AND-CLOSURES-v1.json')
assert source['full_passed'] and len(source['runs'])==143
assert origins['passed'] and actual['passed'] and names['passed'] and natural['passed'] and scope['passed']
assert read('producer-battery-v1.json')['passed'] and read('producer-battery-v4.json')['passed']
assert read('dag-plant-control-v1.json')['passed']
assert all(r['original_reconstructed_exactly'] for r in source['source_records'])
assert len(read('PREMISE-TRACE-v2.json'))==64
assert not origins['actual_direct_custom_axioms'] and not origins['unresolved_actual_dependencies']
trace=read('actual-probe-full-v4.json')
mass=next(r for r in trace if r['id']=='mass_extension_realization' and r['budget']==2)
assert mass['trace'][1]['q']==1 and mass['trace'][1]['actual_return'] is None
result={
 'status':'SCOPED_CONFIRMED_WITH_PRINTED_CONDITIONS_AND_PROVENANCE_QUALIFICATIONS',
 'candidate':{'manifest_sha256':'89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5','payload_entries':540},
 'prerelease_READY':{'sha256':'1c3a10fd1b7da92087e287a18f78c0d831591c343a2c5da0ccc446a694cd3da0','payload_entries':88,'preserved':True},
 'rulings':{
   'literal_forest_soundness':'CONFIRMED; every return executes original state and additional-budget checks; arbitrary ordinary callback',
   'attained_minimum_and_universal_affordable_cover':'CONFIRMED conditional only on printed OrdinaryIH ordinary',
   'separate_DisjointExact_premise':'DISCHARGED by disjoint_exact_of_ordinary ordinary ho in the final theorem',
   'actual_source_replacement_and_budget_recursion':'CONFIRMED in the literal model; every raw occurrence retains exact additional-cost equality',
   'two_actual_raw_core_mass':'CONFIRMED for rational c>=2, duplicate/failing occurrences retained; false extension below c2 rejected',
   'kernel_stored_producer_axiom_scope':'CONFIRMED for exact143 scientific producers, not merely resolved names',
   'source_type_body_correspondence':'CONFIRMED with explicitly retained generated/private/hygienic Name and Name-format qualifications',
   'source_bill_recurrence':'CONFIRMED only under LocalBillBound, c>=2, K>=0, q<=Q and proper state',
   'primitive_source_operation_envelope':'QUALIFIED/OPEN: inspection/check correspondence and callback payload convention remain to justify',
   'polynomial_coefficient_from_ordinary_work_IH':'OPEN',
   'scalar_bit_costs_and_compiled_IR_machine_semantics':'OPEN'},
 'executed':{
   'fresh_positive_scientific_modules':143,'copied_scientific_oleans':0,
   'stored_kernel_occurrences':origins['stored_occurrences'],'unique_kernel_names':origins['unique_stored_names'],
   'resolved_scientific_names':origins['resolved_scientific_names'],'private_kernel_occurrences':origins['private_occurrences'],
   'actual_resolved_proof_body_differences':len(origins['actual_resolved_info_differences']),
   'direct_custom_scientific_axioms':0,'unresolved_kernel_dependencies_or_origins':0,
   'declaration_to_direct_dependency_entries':scope['direct_reference_occurrences'],
   'standard_resolved_axioms':origins['resolved_name_axiom_union'],
   'IR_only_auxiliary_occurrences_no_kernel_type_body':ir['ir_only_name_occurrences'],
   'source_original_hashes_reconstructed':143,'byte_identical_original_adapted_sources':129,
   'import_only_counterparts':14,'raw_exact_import_counterparts':names['raw_exact_import_modules'],
   'qualified_hygienic_import_counterparts':names['qualified_name_only_import_modules'],
   'import_counterpart_declarations_with_Name_differences':names['name_different_stored_declarations'],
   'original_basename_contexts':len(natural['modules']),'unresolved_original_name_structural_differences':len(natural['unresolved']),
   'source_contract_consumer_groups':64,'finite_cases':19,'finite_ordinary_fixture_pairs':60,**actual['counts']},
 'exactness_signature':signature['signatures']['GenericForest.exact_of_ordinary']['binders'],
 'mass_counterextension':{**actual['actual_below_c2_false_extension'],'failed_d1_child_still_counted':True,'context':'post-contact realization of original frozen false-vector control'},
 'open_global_items':['complete ordinary-tree dispatcher','mutual termination','full global runtime','smaller global base','novelty','fresh-context prose/referee framing'],
 'independence':'fresh graph code before candidate contact, same model family/public definitions; post-contact actual-call tracing is not an oracle; no statistical independence or extra replication count',
 'preserved_failures':'all original READY failures and post-release preparation/timeout/representation failures remain with source/log/receipts',
 'skipped_and_platform_limits':'general bootloops-check suite not rerun; ps denied; IR-only machine bodies unaccepted',
 'VERIFIED_CLOSED':False}
(HERE/'REVIEW-RESULT-v1.json').write_text(json.dumps(result,indent=2)+'\n')
report=f'''# Scoped ForestState solver review

The exact v3 generic ForestState solver is CONFIRMED in the literal finite model, conditional only on its printed OrdinaryIH for exact ordinary-tree calls. The final theorem has two explicit binders, ordinary and ho, and derives the older DisjointExact premise internally. Soundness checks every returned forest against the original target/source state and the additional budget. The universal completeness statement covers every affordable agreeing forest and returns an attained minimum.

The fresh isolated rebuild passed all143 positive scientific modules, with zero copied scientific oleans. The stored-producer inventory contains{origins['stored_occurrences']} kernel declaration occurrences and{origins['unique_stored_names']} unique names, including{origins['private_occurrences']} private occurrences. It records seven coalesced proof-body differences with matching exact kinds/types. Direct scientific custom axioms and unattributed kernel dependencies are zero. The standard axiom union is Classical.choice, Quot.sound and propext. Separately,{ir['ir_only_name_occurrences']} compiler IR-only auxiliary occurrences lack kernel type/body records; machine semantics remains unaccepted.

Every original source hash was reconstructed from the released bytes. Of143 source pairs,129 are identical;14 import-only counterparts were separately compiled. Eleven match all type/body records exactly, while three have23 retained generated-Name differences. The15 differing original module basenames were also compiled and compared under explicit root/import Name correspondences. All remaining structural differences are zero. These correspondences are qualified by the recorded compiler Names and Name-representation formatting; raw unequal records remain retained.

The finite actual-call checks passed52 root budget rows across19 small cases:107 visited states,55 raw recursive occurrences,241 child-forest lifts and92 affordable final-forest covers. All actual raw lists, source cut graphs, component-only replacements, exact costs and paid ordinary queries were compared with the graph/partition code prepared before candidate contact. The crossed, sole-hard and three-region minima are1,2 and2. A sole hard call retains q2 on four labels inside five; one-source same-label calls remain an external mutual-induction interface. The60 ordinary table pairs are test fixtures.

The full raw cost vector[1,2,2] has exact mass14/9 at c=3/2, exceeding2/c=4/3; its failed d1 child remains counted. This rejects the extension below c2. The stated rational c>=2 mass theorem is supported. The `(q+1)*K*c^q` result is CONFIRMED as a bound on the defined bill under LocalBillBound, K>=0, q<=Q and proper state. A conservative primitive-operation correspondence, a polynomial K from an ordinary-work IH, scalar bit costs and compiled-machine semantics remain OPEN.

Detailed universal reasoning is in SEMANTIC-REDERIVATION-v2.md; PREMISE-TRACE-v2.md prints64 source-located contract/use groups. ORIGIN-RULING-v3.md and WORK-RULING-v1.md state the provenance and cost qualifications. The original88-payload READY is preserved. New producer controls preceded the first candidate payload contact; later DAG/Name representation checks and the concrete below-c2 realization are explicitly post-contact. Failed preparations and the raw-repr timeout remain retained. The general bootloops-check suite was not rerun, and the platform denied ps inspection.

The ordinary dispatcher, mutual termination, full runtime, smaller global base, novelty and later fresh-context prose/referee framing remain OPEN. This arm claims fresh-code review within the same model family, without statistical independence or an extra replication count. It does not claim VERIFIED-CLOSED.
'''
# Keep counts readable without altering their integer values.
report=report.replace('all143','all 143').replace('contains4977','contains 4977').replace('and4938','and 4938').replace('including571','including 571')
for n in [1375,143,129,14,15,23,52,19,107,55,241,92,1,2,60,64,88]:
    import re
    report=re.sub(r'(?<=[A-Za-z])'+str(n)+r'(?=\b)', ' '+str(n),report)
(HERE/'REVIEW-REPORT-v1.md').write_text(report)
print(json.dumps({'status':result['status'],'result':'REVIEW-RESULT-v1.json','report':'REVIEW-REPORT-v1.md'}))
