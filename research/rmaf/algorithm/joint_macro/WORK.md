# Joint ownership macro route A — workfile v1

Date: 2026-10-14. All three algorithm milestones remain OPEN.

## Pinned objective and scope

Replace the actual reduced two-pendant-cut hard child of the ordinary rooted
MAF scaffold by simultaneous ownership cuts. First target: three parent
components share one T-edge; survivor alternatives split both other source
components across that edge, with every cut and generation/query cost paid.
Critical unresolved case: the three-component overlap chain.

Own paths: `algorithm/joint_macro/` and `results/algorithm-macro-*`.
No unfinished safe-cover work is consumed. X0 fixtures are development input,
not independent certification after contact.

## Total algorithm and reconstruction

OPEN: write rule priorities, applicability, terminal tests, exact fallback,
budget accounting, and reversal of cuts/contractions.

## Universal obligations

OPEN: actual hard-child reachability; exhaustive local ownership coverage;
source-component product splitting; chain case; other hard cases; termination;
all consumer hypotheses; exactness; generation cost; full recurrence.

## First frozen experiment

OPEN: independently freeze and execute n7 comb / Tprime
`[[[[1,3],5],[[2,4],6]],0]`, cherry `[5,6]`, guessed pendants `[1,3]`
and `[2,4]`, both Figure16 orientations, tidying and exact partition/span
checks. No reachability claim before execution.

## Quantified payoff / falsification

Conjectured residual vector `(2,2,2)` gives full `(1,1,4,4,4)`.
This is an arithmetic target only, not a proved cover. Must report its rational
mass at c=231/100 alongside charged construction cost, or retain the smallest
measured witness showing inadequacy.

## Evidence ledger

2026-10-14 first pilot executed with `develop.py`; receipt
`results/algorithm-macro-joint-pilot-v1.json`. Existing X0 24 controls, five
source predicates and four product/mass controls: 33/33. Original receipts
unchanged. Controls and exact partition instrument are now development
contacts, not certification of this design.

The frozen n7 fixture passes every Figure16 step2a–d exclusion in both tree
orientations. Cutting its actual pendant edges gives three raw components;
tidying contracts `[5,6]` and preserves three live components. Raw and reduced
residual optima agree, and all reconstructed optima validate on both original
trees. A common T-edge exists. The three survivor alternatives emit exactly
paid residual `[2,2,2]`, covering all measured optimum partitions; full vector
`[1,1,4,4,4]`, target mass `921759400/949132107`. Runtime 0.007439834s
(single fixture plus controls; no extrapolation to a broad census claimed).

Read-source record: baseline retained v2 text lines 363–495, PDF pp7–9,
and lines 1318–1409, PDF pp24–26. Lemma1's core is coverage by partition
refinement, not cut-set containment. Its construction recursively cuts one
of two oppositely colored pure twigs; the mass at base2 is at most 1/2.
Lemma16 case1 supplies three parents sharing an edge; case2 supplies a
three-parent overlap chain. These are retrieved conditional imports, not
new formal theorems of this route.

Candidate organizing mechanism: for any final agreement partition at most
one final block crosses the shared T-edge. Therefore at most one SOURCE
parent can have a final crossing block. Pick that parent as survivor (or
any survivor if none crosses), and split the other two source parents using
their bipartition cores. The source edge sets are disjoint, so costs add.
This argument is OPEN at the graph/partition correspondence and executable
core completeness interfaces; the abstract cover implication will be kept
separate from those hypotheses in Lean.

## Actual chain development and killed candidate

`CHAIN-PIN-v1.json` n9 source fixture was frozen then executed. It failed
reverse Figure16 step2d at cherry `[0,2]`; receipt
`algorithm-macro-chain-pilot-v1.json` is preserved as inadmissible, not used
as a reachable child.

`CHAIN-PIN-v2.json` n10 fixture passes all parent exclusions and has three
live parents forming a chain. Its two overlap edge pairs have different
four-assignment costs: one has full vector `[1,1,4,4,5,5,5,5]`, exact mass
`655679264200/657748550151 <1`; the other has `[1,1,4,4,4,4]`, mass
`2865278200/2847396321 >1`. Complete finite optimum cover survives at both
pairs; diagonal covers omit some optimum partitions but retain others, so
no optimum-preservation refutation is asserted for that shortcut.
Receipt `algorithm-macro-chain-cover-v1.json`; time0.96969825s.

`CHAIN-PIN-v3.json` n11 fixture passes the actual source regime; C is
non-homeomorphic, so rule7 cannot terminate its connected overlap group.
Every one of its three overlap edge pairs yields full vector
`[1,1,4,4,4,4]` above the target mass. Exact residual optimum3 and witness
reconstruction retained in `algorithm-macro-chain-cover-v2.json`;
time6.06083179s.

Deletion minimization was frozen before execution. v1 tests256/256 subsets
and finds a n9 paid-cover refuter with all-homeomorphic parents; earlier
rule7 solves it, so it is NOT an eligible obstruction at the total macro
call site. That result and its source pin are preserved. Version2 explicitly
excludes earlier rule7 and executes the same256/256 subsets: two eligible
chains, two mass refuters, smallest ten leaves. Scoring took0.0405245s;
the smallest refuter's exact-query *development*
replay took0.853273833s. This is smallest within the pinned deletion family,
not a globally minimum counterexample.

Smallest eligible literal trees:
`T=[1,[2,[3,[4,[5,[6,[7,[8,[9,10]]]]]]]]]`;
`Tprime=[[[[[1,[3,[5,7]]],10],[[2,4],9]],6],8]`, cherry `[9,10]`.
After the two pendant cuts and contraction, live blocks are
`[[1,3,5,7],[2,4],[6,8,9]]`, homeomorphism flags `[true,true,false]`,
exact residual optimum2. Both overlap edge pairs emit four distinct paid2
children. The BB child already realizes the unique optimum; thus no uniform
extra-one-cut continuation charge is possible. Receipt
`algorithm-macro-chain-minimize-v2.json` stores original spans, cuts,
all source tests, exact refinement witnesses, expansions and reconstruction.

KILLED formulation: “every actual chain can choose overlap edges whose
complete four-assignment cut-only ownership cover has full mass<=1 at2.31.”
The above ten-leaf source-reachable, post-rule7 witness refutes it.
This does not refute a topology-aware/terminal-aware macro, the baseline
benchmark, or the user's faster-algorithm objective.

## Formal and workspace validation evidence

`ConditionalCover.lean` compiled with six printed axiom audits, retained in
`results/algorithm-macro-lean-audit-v1.log`. Three-owner cover is an abstract
conditional implication using only standard Lean foundations; chain four-way
cover, cost substitution and three integer mass inequalities use no axioms.
They do not prove graph/state correspondence or Core construction. The
false uniform chain mass plant was compiler-rejected as required; retained
in `algorithm-macro-false-mass-plant-v1.log`. No sorry/admit/custom unproved
axioms/native_decide occurs in the successful file.

`./bootloops-check` was executed. Counts:22 selftest PASS,1 selftest FAIL;
19 partial PASS,2 partial FAIL;3 smoke PASS;3 data-gated refused by design.
Failures: amflow-kit, seedling, tropical-sampler. This route imports none of
those packages and did not modify them. A successful process would not
constitute scientific acceptance; these failures are reported explicitly.

`ALGORITHM.md` gives total candidate priorities, exact edge-enumeration
escape, source fallbacks, reconstruction, consumer hypotheses and charged
recurrence. Eager finite test-core generation is not asserted polynomial;
budget-pruned production generation is an explicit OPEN interface.
No new complete faster bound is claimed. All three milestones remain OPEN.

## Version2 common-edge call-site amendment

The original n7 proposed common-edge fixture has three two-label parents,
hence all are homeomorphic and preceding rule7 solves it. Its receipt and
pin remain unchanged; its role is generator development only. It cannot
support acceleration at the actual post-rule7 SPLIT call.

`COMMON-PIN-v2.json` froze an n8 replacement, then execution confirmed all
parent source exclusions, three live common-edge parents, and homeomorphism
flags `[true,false,true]`. No parent is isolated, and every homeomorphic
subset overlaps the non-homeomorphic parent, so rules6/7 do not apply.
Full vector remains `[1,1,4,4,4]`, exact mass `921759400/949132107 <1`.
Exact residual3 and reconstruction retained; runtime0.022690083s. New receipt
`algorithm-macro-joint-pilot-v2.json` includes the n7 rule7 diagnosis control.

Supplementary actual-chain missing-branch controls were separately frozen
after development (`CHAIN-PLANT-PIN-v1.json`); they do not retroactively
register the earlier search. Both overlap-edge pairs catch deletion of BB,
which raises the residual minimum from2 to3 and loses the literal unique
optimum. Complete cover retains it, and the deliberately false optimum
comparator fires. Receipt `algorithm-macro-chain-plant-v1.json`, two/two
controls. These remain development evidence after contact.
