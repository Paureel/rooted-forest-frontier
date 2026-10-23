# Scaffold adversary workfile

Started 2026-10-15. Owner: fresh independent scaffold adversary.

## Scope and freeze

First contact was `PIN-2026-10-15.md`, read before this workfile. The pin and subsequent literal inputs are declared contacts, not independently generated reference values. Candidate evaluator code, unfinished `universal233/core/`, `universal233/geometry/`, and global continuation work are excluded.

Only this directory and `results/algorithm-scaffold-adversary-*` are owned. No child agents. Algorithm, Correctness, and Smaller base remain OPEN.

## Plan

1. Read applicable instructions, toolkit guide, and required skills.
2. Build and freeze a fresh explicit-graph engine, deterministic colored-core rule, and literal controls before candidate-source contact.
3. Execute controls with clean twins and corruption detection, retaining failures.
4. Read completed candidate/spec and frozen hard-pair literals; fingerprint contacts.
5. Run a small timed graft pilot, document costs before any extension, and retain complete actual-source eligibility diagnostics.
6. Report exact H1 and H2 scope separately, or finite NOFIRE with denominator and failures.

## Running log

- Initial workfile written immediately after the shared pin, before bulk reading.

## Method and independence registration

The toolkit index and recipes were searched for explicit rooted-tree cuts, agreement forests, and graph-span checks. No general BootLoops package supplies this graph instrument; Emitall checks receipt claims but cannot reconstruct graph cuts or source-rule eligibility. A one-shot local falsifier is therefore justified. Existing problem evaluator code will not be read or imported.

The common source-core specification `NEXT-MULTICOLOR-CORE-PIN.md` was read as a declared shared spec before instrument construction. Its tie-break is now frozen: compare normalized homogeneous groups lexicographically by sorted original labels; take the least unique-color group first, otherwise the lexicographically least normalized mixed cherry; recurse on both children in lexicographic order. Deduplicate by original-label partition, retaining minimum true cut charge then lexicographically least source-cut witness. No target optimum is used in this generator.

Engine lineage: fresh Python standard-library explicit directed graphs, exact Fraction masses, fresh rooted restrictions and vertex-minimal spans. Source cuts carry original edge identifiers through unary suppression. Exact depth-zero/one terminal recognition enumerates current source edges only and checks the complete resulting forest. Literal expectations below are constructed mathematical controls, not output regenerated from the engine.

## Frozen literal control expectations (pre-candidate contact)

- Empty, singleton, identical: exact zero further cuts.
- Source ((0,1),2), target ((0,2),1): zero fails, one succeeds.
- Crossed quartet source ((0,1),(2,3)), target ((0,2),(1,3)): partition [{0,2},{1},{3}] is a valid AF; [{0,2},{1,3}] has individually matching restrictions but overlapping source spans and must fail. The two-color core on source, colors 0/2=A and 1/3=B, must cover both extremal source-valid partitions [{0,2},{1},{3}] and [{0},{1,3},{2}]; deleting one mixed branch must miss at least one.
- Unique-color and root suppression: source ((0,1),2), colors 0/1=A and 2=B, emits [{0,1},{2}] with one actual cut. Three distinct colors emit three singletons with two actual cuts. Source ((0,1),(2,3)), colors 0/3=A, 1=B, 2=C emits [{0,3},{1},{2}] with two cuts.
- Bad-charge mutation: a cut witness with two distinct cuts declared charge one is rejected; clean declaration two passes.
- Mass mutation: c=2 and charges [1,1] have mass exactly 1; false mass 3/4 rejected; empty core has mass zero.
- Forest-overlap terminal: on identical crossed-quartet trees, a source forest partition [{0,2},{1,3}] cannot arise by disjoint cuts; the partition-only terminal checker must refuse even though component restrictions match. A valid three-piece twin passes.

All control failures remain archived. Expected values do not change to obtain a pass. Candidate-source contact is forbidden until the engine and these controls are frozen and executed.

### Executed precontact checkpoint

`./bootloops-python research/rmaf/algorithm/scaffold_adversary/controls.py`

```
controls-run-20261015T064755Z.json: passed 23/23, all_pass true
controls-run-20261015T064808Z.json: passed 26/26, all_pass true
```

The second run adds explicit empty forest and actual-source-forest overlap checks (zero fails for span_overlap; one further cut succeeds), without changing any expected values. Both logs retained. `PRECONTACT-FREEZE.sha256` freezes graph code, controls, common core spec, and adversary pin before reading candidate source/receipts. Source eligibility requires source definitions and will be implemented as a separately fingerprinted adapter; no frozen scientific expectation may be changed.

## Source contacts and source eligibility definitions

After PRECONTACT-FREEZE, opened the completed compact scaffold witness and the frozen hard-pair local receipt. Literal inputs and their SHA256 fingerprints are retained in `literal-inputs.json`; their listed masses/optima are retrieved development contacts, not independent reference values. The hard pair's two-cut difficulty will be rechecked with the fresh engine; no evaluator source was read.

Read original `sources/baseline/split-or-decompose-v2.txt`: definitions at PDF pp.3–4, Whidden rule p.6–7, rule4 and rule5 pp.17–18, rules6/7 pp.23–24 and Figure16 p.24. Load-bearing source text: "Apply the first among the following branching rules to be applicable"; Figure16 lists Whidden(t=1), Whidden(t≥3), rule4, rule5 before selected Whidden(t=2). Rule6 requires "overlap on only a single edge" and two homeomorphic/one non-homeomorphic components. Rule7 requires a homeomorphic subset of size at least two with no overlap outside it. These quotes were copied from the opened source bytes.

The fresh source adapter checks every target cherry in both original orientations, excludes common cherries and all earlier Figure16 rules, verifies the selected 8/9 cherry and exactly its actual two pendant groups, applies source cuts, logs all actual unary suppression/common-cherry contractions and singleton deletion, then checks three retained parents with exactly one overlap pair and an isolated homeomorphic third plus rule6/7 exclusion. The full mass retains two original unit branches and two original pendant precuts.

### Pilot registration

Runtime unknown: measuring now on the original literal plus two six-leaf-hard-pair graft orientations at leaf0 (three cases, n10/n15). Real progress is a completed eligible/ineligible case record, checkpointed per case in pilot-progress.json. No extension is authorized by a runtime guess. All original failures will remain in the pilot receipt.

## Executed graft checkpoint

Pilot completed all 3 registered cases. No source-eligibility failures: original n10 and both n15 graft orientations are eligible. Selected 8/9 remains a cherry. Every cherry in both original orientations has exactly two actual pendant groups, with no common cherry, rule4, or rule5. The n15 child has one non-homeomorphic parent on labels {1,2,3,4,10,11,12,13,14,15}, homeomorphic parent {5,6}, and isolated homeomorphic parent {7,8,9}; overlap is exactly the first pair on two target edges. Rules6/7 do not apply.

Executed postcontact source controls: `source-controls-v1.json`, passed 12/12. These controls explicitly catch earlier Figure16 t1/t3/rule4/rule5, selected-cherry failure, common cherry, rule6 single-edge and rule7 closed-homeomorphic overlap. The clean witness passes. The frozen six-leaf pair was rechecked without reading any evaluator: all zero/one source-cut states fail, and source cuts [[2,3],[8,9]] give partition [[0,2,3,4],[1],[5]], proving exact minimum two additional cuts.

Pilot timings on this machine: base 0.0118s; n15 graft orientations 0.0340s and 0.0556s. A repeat with explicit original graph metadata took 0.0108s, 0.0334s, 0.0338s. No extension was needed because both grafts already refute H2. No broad census was launched. Initial successful pilot retained as algorithm-scaffold-adversary-pilot-initial-v1.json; rerun with original graph metadata is algorithm-scaffold-adversary-pilot-v1.json.

### Exact H1/H2 result

Both actual overlap boundaries fail on the graft. Full branch charges (two original endpoints plus two pendant precuts and actual core charge) are:

- target edge [5,7], charges [1,1,3,3], full mass 12857800/12649337; numerator minus denominator = 208463.
- target edge [7,9], charges [1,1,4,5,5,3], full mass 687048104200/686719856393; numerator minus denominator = 328247807.

All 6 core emissions refuse zero/one additional source cuts. H1 FIRE; H2 FIRE for this frozen deterministic generator. The original n10 literal already fires H1 at [5,7], but H2 survives there because the [7,9] remaining full mass is 11857800/12649337. The graft specifically destroys that surviving pretest advantage.

`package_witness.py` reconstructs every emission using original uncontracted graphs and all original source cuts, without depending on tidying to establish the refusals. The complete refusal denominators are 23,23 states for [5,7], and 21,19,19,23 states for [7,9], each including the zero-cut state and every live one-cut edge. Both endpoint one-cut branches separately refuse their own zero/one additional-cut pretests (27 states each), although their two unit charges remain unchanged as required. Integer-only common-denominator recomposition agrees with the Fraction masses. The same hard target/source induced pair appears in all 6 emitted forests (one distinct signature); this is recorded without a caching or speed claim.

Compact executed witness: `results/algorithm-scaffold-adversary-H2-witness-v1.json`, 48558 bytes. It retains original trees/graphs, exact actual source cuts, all overlap boundaries and colors, core histories, contractions and lifts, whole-forest partitions, full pretest witnesses/refusals, integer comparisons, source guard controls, and scope. No failed harness run occurred; all successful runs and receipts remain.

The sufficient colored-core mass certificate is refuted under the stated unchanged endpoint charges and tie-break. Other covers, deeper pretests, different tie-breaks or decomposition algorithms remain untested. Algorithm, Correctness, and Smaller base remain OPEN.

### Supplementary mutation failure and correction

A postcontact group-cut mutation harness initially typed absent edge (1,2), so it raised ValueError before writing the planned receipt. The complete failure and diagnosis are retained in supplementary-group-mutations-failed-01.log. Canonical construction places the {0,1} parent at vertex2 and leaf0 at vertex3; the intended wrong-inside-group edge is (2,3). No scientific expected value changed. The persisted corrected harness group_mutations.py passed 3/3 outcomes: the clean actual one-cut partition equals [{0,1},{2}], while missing the required cut and cutting inside the group both fail that same precontact literal expectation. These postcontact mutation checks are supplementary and do not acquire precontact independence.

## Delivery checks and limitations

- PRECONTACT-FREEZE SHA256 verification passed for all four frozen files after the full run.
- Compact witness integer arithmetic, graph reconstruction, original-label coverage, all6 zero/one-cut refusals, all2 boundaries, and both endpoint zero/one refusals completed in package_witness.py.
- Report-to-witness mass, label, denominator, and refusal comparisons passed. Prose-lint applied to the internal scientific report in two passes: first grammar/claim/number/source scope, then pattern sweep and colleague-language read. No outward-facing novelty or publication claim is made; a fresh-context referee simulation remains outside this internal report.
- The full supplied toolkit suite exited1: 44 package PASS, 3 data-gated REFUSED, 3 FAIL (tropical-sampler os.nice sandbox denial; amflow-kit 7failed/42passed/4skipped, missing /proc in retained failure; seedling cgroup foreign-PID assertion). Its log, all available runner output tails, nonpass details, named skips, absent engines and absent-data checks are preserved locally. No upstream code, verification scripts, integrity pins, or frozen results were edited.
- A `ps` inspection was denied by the sandbox and is irrelevant to the executed mathematical checks. Process activity was never used as evidence of scientific acceptance.
- Final replay instructions and instrument scope are in README.md; exact scientific result and limits are in REPORT.md. DELIVERY.sha256 fingerprints the delivered code, literal contacts, source bytes, controls, report, and compact witness.
