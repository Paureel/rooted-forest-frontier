#!/usr/bin/env python3
"""One-shot reviewed-scope/consumer records and Emitall transcription spec.
No scientific solver. Numbers are checked by Emitall from retained receipts.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT/'research/rmaf/results'
CONF = 'CONFIRMED-SCOPED'
REF = 'REFUTED-AT-WITNESS'
OPEN = 'OPEN-AT-NAMED-OBLIGATION'

def consumer(id, source, required, actual, cost, grade, missing):
    return dict(id=id, source_locator=source, required_hypothesis=required,
                actual_delivered_form=actual, charged_cost=cost,
                verdict=grade, remaining_obligation=missing)

consumers = [
consumer('A.input-priority', 'joint_macro/ALGORITHM.md:10-57',
 'ordinary binary equal labels; q=k-1; fixed-point tidy; all cherries both orientations; rules6/7 before macro',
 'design specifies priorities; frozen fixtures independently tested; no total A0 executor',
 'polynomial input/priority/tidy work per node must be charged', OPEN,
 'source-rule coverage and safe history transport at every priority; implemented total executor'),
consumer('A.Core', 'joint_macro/ALGORITHM.md:64-77; joint_macro/develop.py:26-80',
 'every refining monochromatic partition refines an emitted source-core child; actual cut count after suppression',
 'source Lemma1-inspired generator and finite unique-separator checks; graph theorem absent',
 'all paid internal branches, pruned branches and output serialization; budget pruning required before unbounded generation', OPEN,
 'concrete source-core coverage and generation theorem'),
consumer('A.Joint3', 'joint_macro/ALGORITHM.md:72-79; joint_macro/ConditionalCover.lean:8-23; joint_macro/develop.py:88-106',
 'at most one original source parent owns a crossing final block; independently safe source cores; additive disjoint cuts',
 'conditional ownership theorem plus independently replayed n8 three-child product; implementation eagerly lists cores',
 'three products have residual mass <=3/c^2 only under core theorem; every generation attempt charged', OPEN,
 'original graph/state ownership, core hypotheses, source-history composition and paid lazy implementation'),
consumer('A.Chain4', 'joint_macro/ALGORITHM.md:81-97,127-133; joint_macro/chain.py:14-98',
 'two edge ownership alternatives; sequential refinement with real stage cuts; target full mass <=1',
 'conditional four-way implication and exact n10 counterexample at both edge pairs',
 'vector [1,1,4,4,4,4], mass 2865278200/2847396321 >1 at231/100; all edge-pair attempts paid', REF,
 'replace target-mass claim; no uniform extra-cut charge survives the terminal BB child'),
consumer('A.source-rule-imports', 'joint_macro/ALGORITHM.md:154-160',
 'Whidden/rules4-7/SPLIT/decomposition hypotheses and graph covers, symmetric transport',
 'retrieved source statements and finite priority controls; conditional formal imports',
 'all pretests and source queries retained; unsupported interfaces use design EdgeSearch', OPEN,
 'full original graph interfaces and formal consumer proofs'),
consumer('A.disjoint-query', 'joint_macro/ALGORITHM.md:101-108,142-148',
 'vertex-disjoint embeddings; exact 0/1 pretests; other-component lower bounds; joined valid witnesses',
 'source recursion design only',
 'p>=2: p*T(q-2(p-1)); p=1: T(q-L), L from other components and may be0; all polynomial pretests', OPEN,
 'realized disjoint decomposition and all paid recursion terms'),
consumer('A.escape-reconstruction', 'joint_macro/ALGORITHM.md:18-28,110-116,161-162',
 'every feasible agreement partition has source-cut realization; reverse histories preserve it; well-founded measure',
 'explicit finite edge-subset design and independently checked frozen reconstructions',
 'poly(n)*sum_(j<=q) binom(E,j), E=current source forest edge count; full returned-witness validation; generally n^O(q)', OPEN,
 'universal cut-realization, history/reconstruction and termination theorems'),
consumer('Retarget.rational-arithmetic', 'Retarget233.lean; results/algorithm-review-lean-replay-and-axioms.json:/rows/5',
 'every hard-class recurrence and all generation costs fit a common 2.33 bound',
 'four kernel rational recurrence comparisons only; no source graph/generator premise established',
 'arithmetic alone assigns no cost to unresolved cases', OPEN,
 'all concrete graph/core/generation/scaffold hypotheses; no faster algorithm accepted'),
consumer('B.CLI', 'paid_cover/state_cli.py:15-36; paid_cover/cover_solver.py:48-64',
 'integer nonnegative budget; valid ordinary equal-label forest; initial tree q=k-1',
 'actual 10 controls and 16 reserved optimization calls; forest upper budget n-m; empty 0',
 'parse and every failed budget0..optimum included; recursive parser may exceed Python depth limit', CONF,
 'scope finite tested calls; arbitrary-depth software and universal solver correctness open'),
consumer('B.B1-core', 'paid_cover/cover_solver.py:111-165,230-245',
 'shared vertex >=2 colors; degree3; touching components compatible; actual r-1 source realization; every feasible completion covered',
 'first four predicates checked by source; only two synthetic multicolor states independently replayed',
 'r in{2,3} source realization searches <=2 cuts per color, plus every recursively generated child', OPEN,
 'universal compatible-core cover and transport; original fallback is absent after selected-core failure'),
consumer('B.B2-frontier', 'paid_cover/frontier_cover.py:23-78',
 'at least one original optimum refines a minimum-paid terminal state',
 'five-leaf parent optimum2; both minimum-paid states have total3',
 'minimum selection itself is insufficient; generation and residual solves paid', REF,
 'use different cover selection; failure does not refute existence of a safe cover'),
consumer('B.B3-generate', 'paid_cover/full_cover.py:23-40; paid_cover/frontier_cover.py:23-60',
 'all cutsets<=q; no redundant cuts; actual component increase d; only cheaper coarser terminal domination',
 'actual five-leaf: 37 cut sets tested, 17 terminal partitions, 10 retained states, 180 coarsening scans; 16 reserved cover-set comparisons and 659 child residual checks',
 'H=sum_(d<=min(q,E))binom(E,d) class tests; O(M^2 poly(n)) coarsening; every failed/duplicate state charged', OPEN,
 'universal original graph realization, refinement and suppression/budget transfer; no FPT generation bound'),
consumer('B.B3-complete-fallback', 'paid_cover/full_cover.py:43-63; paid_cover/cover_solver.py:224-268; paid_cover/PIN-v3.md:Coverage argument and exact debt',
 'each retained child completed exactly at q-d; original-state escape exact when no child succeeds',
 'actual calls use solve, which may recurse through select_core and return None without direct edge search; outer call repeats solve',
 'all actual recursive core work and fallback cutsets; PIN binomial-only completion formula needs proof for actual path', OPEN,
 'prove core completeness and charge it, or implement a direct enumerative failure escape'),
consumer('B.reconstruction', 'paid_cover/cover_solver.py:188-211,261-268',
 'disjoint original source spans extend to connected nonempty regions; boundary cuts p-m; valid original labels and budget',
 'BFS reconstructs and rechecks accepted finite outputs; actual cuts independently compared',
 'polynomial BFS/validation per accepted witness', OPEN,
 'universal graph realization and restriction/history theorem'),
consumer('B.terminal-libraries', 'paid_cover/cover_solver.py:217-218,246-256; paid_cover/CONSUMER-TRACE.md:31-32',
 'pure G1-G7 or triple G1-G3 if efficient terminal routines used',
 'library_calls=0; hypothetical ledger only; explicit finite code used',
 'no uncharged library bound imported; actual enumeration/core cost applies', CONF,
 'efficient library implementations and graph hypotheses remain unproved'),
consumer('Balanced.Generate', 'balanced_safe_cover/SPEC.md:7-11,30; balanced_safe_cover/IMPORTS.md:5-8',
 'total oracle-free family; each original nonredundant C<=b; terminal class; original unmarked max d<=b/2 on pure outputs; one original optimum survives',
 'no arbitrary-input efficient generator; finite counterexamples and restricted product only',
 'O*(alpha^b) total generation/recognition/local-witness time and size including rejected candidates', OPEN,
 'construct and prove the guarded efficient generator under original target quantifiers'),
consumer('Balanced.Complete', 'balanced_safe_cover/lean/ConsumerCore.lean:13-44; balanced_safe_cover/CONSUMER.md:5',
 'all completed witnesses valid, exact within their refinement family; one original optimum has a generated ancestor',
 'conditional exact-completion structure and generic one-optimum implication',
 'minimum over every produced completion and all failed calls', OPEN,
 'instantiate validity, minimum and survival from actual original graphs and implemented terminal solvers'),
consumer('Balanced.account', 'balanced_safe_cover/lean/ConsumerCore.lean:46-59; balanced_safe_cover/CONSUMER.md:7-9',
 'm=r+1, p>=m; after tidy m_live+s=r+1; local distance dominated by actual residual cuts',
 'kernel integer identities only; exact finite original-edge controls',
 'r+(p-m)=p-1; reinsert s finished components; original d used for balance', OPEN,
 'nonempty original regions, source cut/component and local-witness realization'),
consumer('Balanced.pure', 'balanced_safe_cover/CONSUMER.md:24-26,38; balanced_safe_cover/IMPORTS.md:9',
 'pure G1-G7, same feasible family under role swap, all marks/rest interactions, original unmarked d_D',
 'conditional import; no actual efficient completion installed by reviewed cover',
 'q_J=h_D(J)-(r_J-1)<=d_D; second mu-(r_prime_J-1)<=d_D; negative refusal; <=2m calls and failed deepening paid', OPEN,
 'concrete marked graph correspondences and exact original-budget completion'),
consumer('Balanced.triple', 'balanced_safe_cover/CONSUMER.md:21-23; balanced_safe_cover/IMPORTS.md:10',
 'component compatible or exactly 3 labels; triple G1-G3, DP and backpointer graph correspondence',
 'conditional import only',
 'input/recognition/reconstruction and every local query included', OPEN,
 'actual arbitrary-depth implementation and concrete graph/executable proof'),
consumer('Balanced.cost-wrapper', 'balanced_safe_cover/CONSUMER.md:32-42; balanced_safe_cover/IMPORTS.md:12-13',
 'O*(alpha^b) generation/output bound and O*(c^(theta*b)) completion; all reduction/reconstruction exact',
 'conditional schema and rational arithmetic certificates, no instantiated generator',
 'O*((alpha*c^theta)^b); budget iteration0..n-1 adds geometric sum for base>1', OPEN,
 'prove all hypotheses and actual charged smaller-base bound'),
consumer('Q.original-edge', 'balanced_safe_cover/quotient/EdgeLocalization.lean:18-63',
 'original edge predicates C subset K; same adjacency in both deletions',
 'kernel theorem Reach(K) refines Reach(C); C union residual equals K deletion',
 'no enumeration bound or optimizer hidden in theorem', CONF,
 'not a terminal/safe-cover generator; original optimum/local graph witnesses still external'),
consumer('Q.half-arithmetic', 'balanced_safe_cover/quotient/EdgeLocalization.lean:86-129; balanced_safe_cover/quotient/RESULT.md:9-13',
 'r>=b-floor(b/2); d<=b-r, with d original local distance justified by graph witness',
 'kernel arithmetic and prose local-witness argument',
 'choosing subset of unknown optimum is existence only; locating K is unpaid and cannot enter production', CONF,
 'graph/local distance inequality and efficient oracle-free enumeration remain open'),
consumer('Q.Q2-ONE', 'balanced_safe_cover/quotient/RESULT.md:15-25; results/algorithm-balanced-cover-verify-witnesses.json:/result/n6',
 'one edge of every optimum quotient leaves original local tau<=floor(b/2)',
 'n6 star optimum 3; all three choices tau 2>1; all three two-cut repairs tau 1',
 'residual +1 for each failed one-edge choice; query work retained', REF,
 'failure is of the proposal; existential cover and reduced-instance target remain open'),
consumer('Q.Q-HALF-ANY', 'balanced_safe_cover/quotient/RESULT.md:27-35; results/algorithm-balanced-cover-verify-witnesses.json:/result/n7',
 'every ceil(b/2)-subset of an optimum is terminal in addition to balanced',
 'efg subset has tau 1 but impure [3,2] overlap and incompatible four-leaf component; ab twin pure',
 'both terminal tests and original unmarked local checks paid', REF,
 'only unrestricted every-subset claim refuted; no certified reduction history; reduced-input one-optimum existential generator remains open'),
consumer('Q.SlowCover', 'balanced_safe_cover/quotient/SlowCover.py:24-66; balanced_safe_cover/quotient/quotient_probe.py:54-81',
 'source cuts distinct/in source; no empty regions; complete valid original agreement certificate',
 'actual four saved cases independently source-replayed, all certificate fields/corruptions checked; universal prose not kernel graph theorem',
 'poly(n)*sum_(i<=min(b,n-1))binom(2n-2,i); zero local optimizer calls; all outputs and rejected candidates paid', CONF,
 'finite code scope only; universal cut realization/reconstruction and arbitrary-depth domain formalization open; licensed bound fails'),
]

claims = [
 ('A.common', CONF, 'algorithm-review-macro-common-n8.json:/prepared,/exact,/children,/vector,/mass'),
 ('A.n7-priority-acceleration', REF, 'algorithm-review-macro-n7-rule7-control.json:/earlier'),
 ('A.chain-target', REF, 'algorithm-review-macro-deletion-family.json:/smallest'),
 ('A.chain-family-denominator', CONF, 'algorithm-review-macro-deletion-family.json:/tested,/eligible_chains,/refuters'),
 ('A.actual-emissions', CONF, 'algorithm-review-macro-actual-emission-check.json'),
 ('A.conditional-Lean', CONF, 'algorithm-review-lean-replay-and-axioms.json:/rows/4'),
 ('A.universal-total-executor', OPEN, 'joint_macro/ALGORITHM.md:154-163'),
 ('Retarget.rational-recurrence-only', CONF, 'algorithm-review-lean-replay-and-axioms.json:/rows/5'),
 ('B.CLI-controls', CONF, 'algorithm-review-paid-cli-controls.json'),
 ('B.reserved-general-execution', CONF, 'algorithm-review-paid-reserved-final.json'),
 ('B.reserved-hard-child-evidence', OPEN, 'algorithm-review-paid-reserved-final.json:/eligible_initial_2e=0'),
 ('B.every-reserved-child-residual', CONF, 'algorithm-review-paid-every-child-progress.json'),
 ('B.B1-unrestricted-gain', REF, 'algorithm-review-paid-B1-invocation.json'),
 ('B.B2-minimum-frontier', REF, 'algorithm-review-paid-B1-B2-B3.json:/exact_parent,/B2'),
 ('B.B2-smallness-through4', CONF, 'algorithm-review-B2-smallness-through4.json:236 nonempty pairs plus 1 empty plumbing pair'),
 ('B.B3-finite-repair', CONF, 'algorithm-review-paid-B1-B2-B3.json:/B3'),
 ('B.B3-mass-certificate', REF, 'algorithm-review-paid-B1-B2-B3.json:/B3/mass'),
 ('B.copy-corruptions', CONF, 'algorithm-review-copy-bugreports.json'),
 ('B.finite-model-Lean', CONF, 'algorithm-review-lean-replay-and-axioms.json:/rows/1,/rows/3'),
 ('B.universal-core-and-cost', OPEN, 'paid_cover/cover_solver.py:230-245;paid_cover/full_cover.py:51,62'),
 ('Balanced.nine-fixtures', CONF, 'algorithm-balanced-cover-verify-fixtures-v2.json'),
 ('Balanced.equal-halves-safety', REF, 'algorithm-balanced-cover-verify-fixtures-v2.json:/result/equal_halves_n4'),
 ('Balanced.product-r0-r2', CONF, 'algorithm-balanced-cover-verify-product-r2.json'),
 ('Balanced.parent-kernel-constituents', CONF, 'algorithm-balanced-cover-verify-lean.json:/reports'),
 ('Q.original-edge-and-arithmetic', CONF, 'algorithm-balanced-cover-verify-lean.json:/reports/9,/reports/10'),
 ('Q.Q2-ONE', REF, 'algorithm-balanced-cover-verify-witnesses.json:/result/n6'),
 ('Q.Q-HALF-ANY', REF, 'algorithm-balanced-cover-verify-witnesses.json:/result/n7'),
 ('Q.actual-slow-source-four-controls', CONF, 'algorithm-review-continue-slow-source-replay.json'),
 ('Balanced.Q.efficient-guarded-generator', OPEN, 'balanced_safe_cover/quotient/RESULT.md:53-57'),
]

envelope = {
 'review': 'continuation-2026-10-15',
 'provenance': 'same interrupted independent A/B and balanced/Q reviews; no extra replication count',
 'claim_vocabulary': {CONF:'only named finite/kernel/source scope', REF:'named proposal/certificate rejected at exact witness', OPEN:'required named theorem or implementation absent'},
 'all_three_main_milestones': {'complete_algorithm':'OPEN', 'universal_correctness':'OPEN', 'smaller_base':'OPEN'},
 'unfinished_construction_read': False,
 'novelty_or_faster_algorithm_claim': False,
 'evidence': 'research/rmaf/results/algorithm-review-continue-reconciliation-v4.json',
 'negative_control_provenance': 'research/rmaf/algorithm/verification/continuation-2026-10-15/FALSE-CONTROL-PROVENANCE.json',
 'consumer_trace': consumers,
}
(HERE/'CONSUMER-TRACE.json').write_text(json.dumps(envelope,indent=2)+'\n')
verdict = {k:v for k,v in envelope.items() if k != 'consumer_trace'}
verdict['claims'] = [dict(id=id, verdict=grade, evidence_locator=loc,
                          provenance='new bounded source replay in same continued review' if id=='Q.actual-slow-source-four-controls' else 'continued inspection of retained independent evidence/source')
                     for id,grade,loc in claims]
verdict['card_corrections'] = [
 'mark frozen release review complete only at scoped review level; keep all 3 main milestones OPEN',
 'stale WORKFILE/JOURNAL pending labels are historical; final balanced Lean receipt is passed and v1 detector receipt remains retained',
 'record actual B core-recursive failure/fallback and cost obligation; no direct edge escape assumed',
 'append Q RESULT line31 omitted-target-b erratum using source geometry_probe.py:44 and independent n7 receipt',
 'keep all minimality claims at their enumerated families; no Q five-leaf independent census claim',
]
(OUT/'algorithm-review-continue-verdict.json').write_text(json.dumps(verdict,indent=2)+'\n')

spec = {'campaign':'frozen review continuation transcription only',
        'register':'exact stored receipt values; not new mathematical certification',
        'quote_source': str((HERE/'VERDICT.md').relative_to(ROOT)),
        'receipts': {},
        'defaults':{'mode':'exact'},'claims':[]}
# pathlib.relative_to cannot traverse upward; receipt paths are absolute local
# paths below. They never leave the user's permitted workspace.
for alias, name in [('r','algorithm-review-continue-reconciliation-v4.json'),('a','algorithm-review-lean-replay-and-axioms.json'),('b','algorithm-balanced-cover-verify-lean.json'),('s','algorithm-review-continue-slow-source-replay.json')]:
    spec['receipts'][alias] = {'path':str(OUT/name)}
spec['receipts']['smallness'] = {'path':str(OUT/'algorithm-review-B2-smallness-through4.json')}
quoted = [
 ('r','/summary/A_common/residual','3'), ('r','/summary/A_common/mass','921759400/949132107'),
 ('r','/summary/A_chain/tested','256'), ('r','/summary/A_chain/eligible_chains','2'),
 ('r','/summary/A_chain/refuters','2'), ('r','/summary/A_chain/smallest_n','10'),
 ('r','/summary/A_chain/exact/residual','2'), ('r','/summary/A_actual_emission/actual_stage_cut_checks','16'),
 ('r','/summary/B_parent/cuts','2'), ('r','/summary/B3/tested','37'),
 ('r','/summary/B3/terminals','17'), ('r','/summary/B3/scans','180'),
 ('r','/summary/B3/mass','126200/53361'), ('r','/summary/B_reserved/completed','16'),
 ('r','/summary/B_reserved/passed','16'), ('r','/summary/B_reserved/eligible_initial_2e','0'),
 ('r','/summary/B_reserved/all_children','659'), ('r','/summary/balanced_fixture_count','9'),
 ('r','/summary/balanced_equal_halves/optimum_cuts','1'),
 ('r','/summary/balanced_equal_halves/optimum_partition_count','3'),
 ('r','/summary/balanced_equal_halves/surviving_optimum_count','0'),
 ('r','/summary/balanced_equal_halves/charged_total','2'),
 ('r','/summary/Q_n6/optimum','3'), ('r','/summary/Q_n6/optimum_realizations','19'),
 ('r','/summary/Q_n7/optimum','2'),
 ('a','/candidate_accepted_distinct_statements','24'), ('a','/dependency_statements','21'),
 ('a','/audit_duplicate_prints','10'), ('b','/route_statements','30'),
 ('b','/quotient_statements','12'), ('b','/false_controls_rejected','7'),
 ('b','/status','passed'),
]
for alias,pointer,value in quoted:
    spec['claims'].append(dict(section='retained values',label=alias+pointer,
                               quoted=value,expr=f"f('{alias}','{pointer}')"))
spec['claims'].append(dict(section='identity',label='pin entries',quoted='81',expr="len(f('r','/pin_checks'))"))
spec['claims'].append(dict(section='slow code',label='control case count',quoted='4',expr="len(f('s','/rows'))"))
spec['claims'].append(dict(section='B2 smallness',label='nonempty pairs',quoted='236',expr="f('smallness','/pairs')-f('smallness','/rows/0/pair_count')"))
spec['claims'].append(dict(section='B2 smallness',label='empty plumbing pair',quoted='1',expr="f('smallness','/rows/0/pair_count')"))
(HERE/'CLAIMS.json').write_text(json.dumps(spec,indent=2)+'\n')
control = {'campaign':'post hoc transcription comparator control only',
           'receipts':{'s':{'path':str(OUT/'algorithm-review-continue-slow-source-replay.json')}},
           'claims':[{'label':'four-case clean control','mode':'exact','quoted':'4','expr':"len(f('s','/rows'))"}]}
(HERE/'CLAIMS-CONTROL-CLEAN.json').write_text(json.dumps(control,indent=2)+'\n')
control['claims'][0]['quoted'] = '5'
(HERE/'CLAIMS-CONTROL-CORRUPT.json').write_text(json.dumps(control,indent=2)+'\n')
print(json.dumps({'consumer_sites':len(consumers),'scoped_claims':len(claims),'transcription_claims':len(spec['claims'])}))
