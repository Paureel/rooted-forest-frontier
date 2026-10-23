#!/usr/bin/env python3
"""Source-bound interface rulings; statements and obligations kept separate."""
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
claims = []
def claim(name, grade, source, use, hypotheses, delivered, cost, remaining='', witness=''):
    claims.append({'id': name, 'verdict': grade, 'source_locator': source,
                   'consumer_locator': use, 'exact_hypotheses': hypotheses if grade == 'CONFIRMED-SCOPED' else [],
                   'unproved_consumer_requirements': hypotheses if grade == 'OPEN-AT-NAMED-OBLIGATION' else [],
                   'delivered_form': delivered, 'cost_scope': cost,
                   'remaining_obligation': remaining, 'witness': witness})
C='CONFIRMED-SCOPED'; O='OPEN-AT-NAMED-OBLIGATION'; R='REFUTED-AT-WITNESS'
claim('source-partition-from-checks', C, 'SourceBridge.lean:243-311', 'InitialLift.lean:88-112,127-138;Controls.lean:13-20,51-58',
      ['partitionCheck (leaves t) bs=true', 'pairwiseEmbeddings t bs=true'],
      'Constructed actual source supports, one-edge connected walks, terminal ownership and disjointness; no supplied connectedness/convexity field',
      'noncomputable proof witness, not production partition search', 'two-tree restriction agreement and generate label guard remain separate')
claim('original-terminal-owner-iff', C, 'SourceBridge.lean:271-302', 'InitialLift.lean:110-112,134-138',
      ['the two exact Boolean source checks', 'actual original leaf occurrences u/x and v/y'],
      'owner equality iff original labels share a supplied block; block monochromaticity separately gives source monochromaticity',
      'logical correspondence only', 'not owner equality at arbitrary nonterminal vertices')
claim('homogeneous-same-graph-coarsening', C, 'CherryCoarsening.lean:13-16,99-204', 'Normalization.lean:133-145',
      ['actual source partition', 'actual homogeneous cherry', 'monochromatic partition'],
      'Constructed monochromatic coarsening; parent in a third support handled by deleting its pendant excursion',
      'no implementation operation count or original cut asserted')
claim('actual-cherry-quotient', C, 'Contraction.lean:110-177', 'Normalization.lean:133-145',
      ['actual CherryContraction', 'source partition with the two cherry leaves in one owner'],
      'Delete the two old terminal vertices, retain valid supports, prove connected walks and original terminal owner lift',
      'graph quotient proof; original residual-cut realization separate')
claim('normalization-transport', C, 'Normalization.lean:99-105,130-207', 'InitialLift.lean:128-138;CutRecords.lean:220-224',
      ['SourcePartition (skeleton t)', 'Monochromatic P id'],
      'Exact normalize is composed actual homogeneous rewrites; every old payload is contained in its mapped new payload and old owner equality implies new owner equality',
      'syntactic payload/purity invariants exist; per-prefix work bound absent', 'no converse owner equality or group bijection')
claim('initial-original-label-normalization', C, 'InitialLift.lean:88-138', 'CutRecords.lean:240-257',
      ['the two exact Boolean source checks', 'each original block monochromatic under color'],
      'Original taxa survive inside mapped normalized group payloads; common original block labels map to equal owners',
      'logical original-label lift, no original residual-component certificate')
claim('unique-color-selected-singleton', C, 'Branches.lean:60-118', 'CutRecords.lean:227-230',
      ['origins t Nodup', 'actual monochromatic source partition', 'choose t=one g'],
      'Actual selected group occurrence is current nonroot and a singleton owner',
      'actual color-filter/membership scans still require accounting')
claim('mixed-cherry-singleton-alternative', C, 'Branches.lean:175-210', 'CutRecords.lean:231-234',
      ['actual monochromatic source partition', 'choose t=two a b'],
      'One of the two actual nonroot grouped cherry leaves is a singleton for the supplied target partition',
      'two attempted children in exact step; no claim both preserve target')
claim('normalized-chooser-no-refusal', C, 'Branches.lean:212-282', 'CutRecords.lean:235-236',
      ['FullyNormalized t, derived for normalize current'],
      'Exact chooser has no refuse result', 'no output existence or source-component assertion')
claim('erase-and-suppression-transport', C, 'Suppression.lean:95-103,142-233;EraseLift.lean:40-87,163-180', 'CutRecords.lean:183-185',
      ['origins t Nodup', 'actual current nonroot selected group occurrence', 'monochromatic source partition', 'chosen owner is singleton'],
      'Exact erase returns nonempty tree; new source supports are terminal hulls; unchanged groups survive with owner equality under new-to-old display embedding; chosen owner has no surviving terminal',
      'new displayed paths embed in old paths; not one-edge cost or original residual realization')
claim('origin-and-cut-guard-invariants', C, 'Origins.lean:24-136;CutRecords.lean:22-161', 'CutRecords.lean:181-185,221-223,254-257',
      ['fromTree for initialization', 'Nodup/RootZeroOnly/CutsAvoid premises for their preservation', 'explicit original-origin sublist for reachable_origins_actual'],
      'Nodup origins, root-zero restriction and old-cut absence are initialized/preserved; sublist membership gives actual original vertices',
      'identifier invariants only', 'named-original reachability and full residual edge membership not consequences of the three local guards alone')
claim('exact-attempt-continuation', C, 'CutRecords.lean:166-202', 'CutRecords.lean:229-234',
      ['arbitrary continuation f', 'Nodup origins', 'RootZeroOnly t', 'CutsAvoid t cuts', 'monochromatic source partition', 'actual nonroot selected singleton group'],
      'All three actual refusal guards are discharged; literal continuation receives exact next/group/cut arguments and local source transport is constructed',
      'one childAttempt is added; nothing about correctness/output of f', 'original edge residual component theorem remains OPEN')
claim('local-step-and-initial-composition', C, 'CutRecords.lean:209-257', 'CoreProgram.lean:108-122;integration/FIRST-GAP.md:8-48',
      ['arbitrary f', 'the three local origin invariants and monochromatic source partition', 'initial variant constructs these from Boolean checks and original block monochromaticity'],
      'Finish or an existential target-preserving chosen singleton with SourceAttempt; SourceAttempt is constructed, never assumed',
      'no theorem here consumes this local result into finite-budget run coverage', 'OPEN-FINITE-BUDGET-COVERAGE')
claim('recorded-charge-and-prefix-counts', C, 'CoreInvariants.lean:61-62,118-173;CoreProgram.lean:163-237', 'integration/FIRST-GAP.md:45-60',
      ['emitted output membership for syntactic output claims', 'exact run q for visited/attempt count bounds'],
      'Recorded names nonroot/Nodup; pieces=recorded cuts+1; visited+attempts+3 <= 3*2^(q+1)',
      'combinatorial prefix/attempt counter only; failed and pruned attempts included', 'graph nonredundancy, polynomial operation work, raw mass and full outer recurrence unproved')
claim('original-residual-components', O, 'integration/FIRST-GAP.md:24-48', 'CoreProgram.lean:105;finish emission:112',
      ['required: actual reachability from a proper original source'],
      'No residual-component bijection or exact split-label theorem delivered',
      'must establish selected original edge is live, split is leaf-bearing, detached components unchanged and finish matches output', 'OPEN-ORIGINAL-RESIDUAL-COMPONENTS')
claim('finite-budget-coverage', O, 'integration/FIRST-GAP.md:50-56', 'CoreProgram.lean:120-126',
      ['required: finite terminal-owner measure and composed original-label lifts'],
      'No output existence/refinement coverage theorem for budget-pruned run',
      'budget clipping and pruning are executable, not correctness evidence', 'OPEN-FINITE-BUDGET-COVERAGE')
claim('realized-cost-mass-work', O, 'integration/FIRST-GAP.md:58-60', 'whole source-core and outer macro consumer',
      ['required: realized original cuts, complete source cover, full generation/implementation work accounting'],
      'No universal realized cost>=r-1, raw mass bound or polynomial per-prefix work theorem',
      'list/tree scans, coarsening recognition, all pruned prefixes and original reconstruction require accounting', 'OPEN-REALIZED-COST-MASS-WORK')
claim('whole-algorithm', O, 'TARGET.md:5-13;integration/RESULT.md:3-6', 'all three main milestones',
      ['complete rules/priority/terminal/reconstruction', 'universal optimum survival and termination', 'complete charged smaller-base recurrence'],
      'No complete solver, universal correctness or smaller base accepted',
      'local source progress is one interface', 'all three main milestones OPEN')
claim('stronger-owner-converse', R, 'Normalization.lean:99-105', 'hypothetical strengthening, not a frozen theorem', [],
      'Homogeneous contraction can merge different fine owners', 'no extra cut charged by this witness',
      witness='CONTROL-PIN normalization-does-not-preserve-every-fine-owner; ScopeWitnessesV2 homogeneous_projection_is_not_injective')
claim('both-mixed-candidates-singletons', R, 'Branches.lean:203-210', 'hypothetical strengthening, not a frozen theorem', [],
      'On the five-leaf parity chain only chosen group3 is a target singleton; group4 belongs to [0,2,4]', '',
      witness='ScopeWitnessesV2 one_target_singleton_not_both; fresh semantic W4')
claim('local-success-implies-budget-output', R, 'CutRecords.lean:209-219', 'hypothetical strengthening, not a frozen theorem', [],
      'Two differently colored leaves, budget0: erase succeeds but output/refusal lists empty, visited1/attempts1/pruned1', '',
      witness='ScopeWitnessesV2 budget_zero_local_success_without_output; fresh semantic W3')
claim('local-origin-guards-imply-original-reachability', R, 'CutRecords.lean:209-212', 'hypothetical omission of original reachability', [],
      'Forged origin000 passes local invariants and reaches continuation, while invalid in the separately named two-leaf original tree; state explicitly unreachable', '',
      witness='ScopeWitnessesV2 local_origin_guards_do_not_imply_named_original_reachability; fresh semantic W5')
claim('raw-checks-imply-generate-accepts-labels', R, 'SourceBridge.lean:306-311;CoreProgram.lean:124-126', 'hypothetical full-wrapper strengthening', [],
      'Duplicate original labels pass raw source checks but generate rejects duplicate original label', '',
      witness='ScopeWitnessesV2 proper_label_generate_guard_is_separate; frozen duplicate-tree-labels-raw-boolean-is-not-instance')
payload = {'scope': 'same-lineage source-bound frozen integration review; zero additional replications',
           'manifest': 'research/rmaf/algorithm/universal233/INTEGRATION-MANIFEST-v1.json',
           'all_main_milestones': {'complete_algorithm':'OPEN','universal_correctness':'OPEN','smaller_base':'OPEN'},
           'claims': claims, 'source_core_or_full_solver_accepted': False,
           'source_locator_base': 'research/rmaf/algorithm/universal233/integration/',
           'source_roots': {'integration':'research/rmaf/algorithm/universal233/integration/',
                            'core':'research/rmaf/algorithm/universal233/core/',
                            'geometry':'research/rmaf/algorithm/universal233/geometry/',
                            'original_RMAF':'research/rmaf/lean/RMAF.lean',
                            'main_TARGET':'research/rmaf/algorithm/TARGET.md'},
           'unread_exclusions': ['live cut_realization', 'live source_coverage', 'profile/exchange/cherry-selection extensions', 'main WORKFILE']}
(HERE / 'CONSUMER-TRACE.json').write_text(json.dumps(payload, indent=2) + '\n')
(ROOT / 'research/rmaf/results/algorithm-integration-fresh-review-verdict.json').write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps({'consumer_claims': len(claims), 'grades': {g:sum(c['verdict']==g for c in claims) for g in [C,R,O]}, 'all_main_milestones':'OPEN'}))
