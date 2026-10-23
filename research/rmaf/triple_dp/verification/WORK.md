# Fresh triple-DP verifier work log

Opened 2026-10-14 after reading `research/rmaf/spec.json` first.

Scope: ordinary rooted MAF completion, no rho leaf; already-cut source forest; every incompatible source component has exactly three leaves; compatible components may be larger. Verify candidate characterization by an independent leaf-partition / rooted-triple / direct-path oracle, authored and frozen before reading any production implementation. Do not read pure_bridge work or existing oracle/verification implementations. Later comparison may import only `research/rmaf/triple_dp/solver.py`; later proof-scope inspection may read `TripleDP.lean`.

Finite tests do not establish the graph correspondence or the full theorem. Particular attacks: source embedding disjointness in compatible components, sufficiency of root boundary state, and rejection of deliberately corrupted outputs.

Initial provenance: author implementation unseen; reference expected answers must not be tuned from solver output. Planned controls are hand positive, malformed, wrong-result, and mutant/clean-twin pairs, frozen before runs.

## Method and preregistration (before implementation access)

The toolkit index was searched by tree/phylogeny/partition/exact/graph capability. Gatekeeper's complete guide was read; it gates numerical fits and does not supply a rooted-tree partition oracle. The fresh implementation is deliberately problem-specific and independent, required by the verification assignment; no production or existing oracle code is reused.

The exact oracle will enumerate all leaf set partitions by restricted growth, compare rooted restrictions by the displayed rooted-triple signatures, and test minimal embeddings by explicit unions of unique paths between leaf vertices. It does not enumerate cut-edge sets. All arithmetic is discrete and exact; no numerical tolerance exists. The reference is authored before viewing `solver.py` or `TripleDP.lean`. Shared layers are the mathematical input convention, nested-tree JSON, Python standard library, and machine; these do not provide independence from a mistaken convention in the spec itself.

Frozen controls: singleton (1 component, 0 cuts); identical balanced quartet (1, 0); incompatible triple (2, 1); crossing source pairs (3, 1); compatible four-leaf component with an interspersed foreign leaf (2, 0); pair spanning the target root plus a singleton (2, 0). Malformed controls: repeated target label, repeated source label, missing source label, unary internal node, empty source forest; each must raise ValueError. Wrong-result controls: wrong optimum count, missing/duplicate leaf, an incompatible full triple, and two crossing blocks; each must fail. Deliberate mutant merges an incompatible triple intact (1 instead of 2); its clean twin is the two-component hand solution. An additional deliberate mutant ignores target vertex overlap for crossing pairs (2 instead of 3), with a hand three-component twin. Hand expectations are fixed in controls.json.

Run plan: controls first; then a bounded pilot over n<=4 and 20 uniformly selected n=5 generated cases before full enumeration. Real progress units are comparisons completed and candidate-characterization partitions checked. Full run, if projected short, covers every unordered rooted binary target tree on fixed labels n=1..5 and every source forest in regime. Large source blocks are forced to their target restriction; blocks of size<=3 range over all rooted binary trees. Expected total derived combinatorially: 10029 solver cases (1+2+21+345+9660); otherwise stop and diagnose denominator drift. Any counterexample stops the verification. No change to reference answers based on solver output is permitted.

## Executed controls and pilot

Oracle controls passed before the first production import; receipt `research/rmaf/results/triple-dp-verification-controls.json` records exact hashes and 6 positive / 5 malformed / 5 wrong-result controls, including 2 deliberately failing mutants and 2 clean twins. Then production was accessed only by importing `solver.py`, with no source reading and no imported oracle.

Pilot (same code/settings/machine) completed 389 production comparisons with zero mismatches. Its uniformly sampled 20 n=5 cases took 0.003758957998797996 seconds; linear projection for 9660 n=5 cases is 1.8156 seconds, with no claim of an asymptotic scaling law. Startup is excluded by using the timed n=5 loop. Smaller-stage costs are retained in the pilot receipt. The measured runtime supports the planned full bounded run. Frozen oracle/control hashes are in PRE_SOLVER_SHA256.txt; neither file was changed after production import.

## Bounded finite result

The full run passed 10,029/10,029 solver comparisons and 70,660/70,660 monochromatic-partition characterization checks in 1.517521375000797 seconds. Counts by n: 1, 2, 21, 345, 9660. Cases containing a bad triple: 4,326; cases containing a compatible component with at least four leaves: 645. Both source and target vertex disjointness were tested directly, using independent vertex sets in the oracle. Every returned partition was checked for complete unique leaf coverage, source ownership, rooted-triple agreement, target/source path disjointness, optimum component count, and additional_cuts = components - number_of_source_components.

The controls were also run through the production `solve` entry point: 6 positive and 5 malformed controls passed. The comparator caught all 5 frozen wrong results, including 2 deliberate mutant outputs; both clean twins passed. The two mutants are output-level behavioral mutations (retain a whole bad triple; ignore target overlap), not altered copies of production code. 

Script-of-record: `./bootloops-python research/rmaf/triple_dp/verification/run_verification.py --mode full --output research/rmaf/results/triple-dp-verification-full.json`. The receipt records `oracle_sha256`, `controls_sha256`, `harness_sha256`, and `solver_sha256`. The hashed oracle file contains the instance generator. Oracle and controls still matched PRE_SOLVER_SHA256.txt after the full run. No reference was changed after production access. The solver source was never read; only its module was imported for `solve`.

Verbatim receipt summary:
```
"finite_verdict": "PASS"
"failures": []
"seconds": 1.517521375000797
"theorem_verdict": "OPEN"
```

## Source-disjointness attack and precise remaining lemma

INFERRED, not a formal theorem: the compatible-component bridge should be stated explicitly. Let T be a rooted binary target, C a source component's leaf set, and S a rooted labeled tree isomorphic to T restricted to C. For all pairwise disjoint nonempty A_i subsets of C, pairwise disjoint minimal connecting vertex sets E_T(A_i) imply pairwise disjoint E_S(A_i), and S restricted to A_i is isomorphic to T restricted to A_i. This must be proved for vertex disjointness, not just edge disjointness.

The reason suppression is the critical check-site is that T|C contracts unary path segments. For a block of at least two leaves, the root of its minimal embedding is an LCA of C leaves and survives suppression; all terminal leaves survive too. Thus an embedding uses a whole retained-vertex path segment, never only a strict middle portion with newly created endpoints. This is the intended route to exclude collisions introduced by contraction. It is a proof sketch only. The bounded oracle failed to falsify this implication in the full stated finite domain.

For a bad three-leaf source component, a proper block has size one or two. All rooted binary restrictions on a fixed set of at most two leaves are isomorphic, and every proper partition has at most one non-singleton block. The third leaf cannot lie on a path joining the other two because it is a leaf vertex. These facts explain why prohibiting the whole triple can suffice locally; no unrestricted larger incompatible component is covered.

## Root boundary-state attack and precise remaining lemma

A full correspondence needs an explicit graph invariant, absent from the generic automaton theorem: for each subtree root v, state bottom means v is unused; a non-bottom state marks exactly one root-containing region whose leaves have one source color, with the actual proper subset mask for a bad color. Every region must contain at least one labeled leaf. Closed regions are minimal connecting subtrees; the open region may be its minimal subtree plus the path to v. Cost is the number of closed regions, and finishing charges one for a nonempty open region.

Required theorem: every feasible graph configuration under that invariant decomposes into at least one legal close/propagate/merge transition, and every legal transition reconstructs such a configuration, preserving leaf coverage, vertex disjointness, proper bad masks, and the closed-region cost. This theorem must quantify over all good colors and all bad colors simultaneously. In particular, propagating an open child must be allowed to add a stem through v even when the current leaf block's minimal embedding does not contain v. Conversely no empty root-containing region may be charged as a component. The root finalization must remove any surplus stem without changing the leaf partition or component count.

This graph-to-state theorem, plus the compatible-source embedding lemma above, remains OPEN. The generic min-plus optimality result cannot substitute for either implication.

## Lean inspection and kernel replay

READ at SHA256 cbe161314dd8282e86ec2be100898f0b24b5967262e35c006275d1b7cf66ff8c. `TripleDP.lean` lines 3–6 explicitly say: "The correspondence from graph agreement forests to these automaton rules is NOT asserted here." Lines 22–27 define `Derives` solely from supplied `initial` and `rules`; lines 51–55 prove minimum attainment and domination for those supplied rules. Lines 96–116 derive optimality and no-derivation equivalence. This is generic automaton correctness, conditional on the transition relation representing the intended graph problem.

Lines 172–195 supply one bad-color rule system and a three-leaf exact control. Lines 206–209 explicitly define LCAClosed as a necessary property, not equivalence to connectedness. Lines 211–230 show consequences of LCA closure and of an already supplied disjointness hypothesis. They do not construct graph regions or establish the necessary correspondence. Lines 232–253 prove arithmetic state/transition bounds for their defined expressions; they do not establish an implementation's worst-case runtime by themselves.

Executed `.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean research/rmaf/triple_dp/TripleDP.lean`; kernel compilation succeeded, with real time 0.56 seconds from `/usr/bin/time -p`. Log: `research/rmaf/results/triple-dp-verification-lean.log`. All 19 printed axiom audits used only subsets of propext, Classical.choice, Quot.sound, or no axioms. Source grep found no sorry/admit/unsafe/custom axiom declaration. Non-failing constructor-name lint warnings are retained in the log.

A post-inspection exact scope witness in `lca_gap_witness.py` confirms that region {root, left-left grandchild} is LCA-closed but disconnected because the left child is missing. Its expected Boolean results were written before execution. Receipt: `research/rmaf/results/triple-dp-verification-lca-gap.json`. This is NOT a counterexample to the Lean statements; it demonstrates why the formalized LCA property cannot silently stand in for graph connectedness.

## Independence limits and final verdict

The verifier authored no production code or proof and read no pure_bridge material or existing oracle/verification implementation. The fresh oracle and frozen controls were saved to disk and hashed before the first production import. The production code and oracle share the task's ordinary rooted no-rho conventions, exact input leaf labels, Python runtime, and basic mathematical tree semantics; they do not share implementation routines, cut-set enumeration, DP recurrence, caches, generated reference outputs, or expected answers. The checker uses rooted-triple signatures rather than production restriction output. The correctness of rooted-triple characterization itself has not been kernel-formalized here.

The oracle references first contacted the production claim in the pilot/full comparisons on 2026-10-14 and are now consumed for this solver hash. If these outputs guide a production revision, rerunning the same cases becomes regression evidence, not fresh held-out certification of that revision. Any future fresh certification needs untouched cases or a fresh route.

Limits: n<=5 cannot contain two bad triples; it cannot test arbitrarily large compatible components. Exhaustiveness is over fixed labels and unordered rooted binary shapes, with every source forest in the stated regime, not over malformed encodings or nonbinary trees. The source/target input convention itself is shared. Output-level mutants test the checker, not production's internal mutation sensitivity. No global sub-2.3391 recurrence, novelty claim, original-k theorem, or source-paper reading was attempted. The repository-wide bootloops-check suite was not run by this narrow verifier; the retained task-specific exact battery and Lean invocation were run.

VERDICT: finite verification PASS for the pinned solver hash; kernel-checked generic automaton and listed support lemmas reproduce; universal ordinary-MAF completion correspondence OPEN at the two graph lemmas above. No scientific closure is claimed from finite tests.


## Report checks

Two prose passes checked scope, count units, exact receipt totals, and the distinction between finite comparisons and a universal theorem. A separate fresh-context referee-sim audit is in `referee_sim_WORK.md`. Its recommended scope and preservation edits were applied: README now states n<=5, the inability to contain two bad triples, the 10,029-case/70,660-partition denominator, the pinned solver-hash field, and separate replay output paths. WORK names the actual recorded hash fields. No reference data, controls, comparison code, or numerical result changed during these edits.

## Concurrent Lean edit and separate replay

The final hash comparison found that the parent had renamed local Mask variables from a/b/c to x/y/z in TripleDP.lean while this report was being finished. The solver, oracle, controls, and comparison harness retained their original hashes. The revised Lean file was read in full and compiled separately; `research/rmaf/results/triple-dp-verification-lean-replay.log` records a successful 0.55-second compile, all 19 axiom reports, and no lint warnings. The revised source hash is 6b544504b68dd6638caa40200914dee5720be1cdc38ce5f180de1dc792944298. The theorem statements retain the same mathematical scope and the graph correspondence remains OPEN.

The revised source is saved as `verification/TripleDP.checked.lean`. Reversing the five recorded local-renaming edits reconstructs `verification/TripleDP.initial-checked.lean`, whose SHA256 was checked exactly against the original cbe161…ff8c receipt. This confirms that the only intervening source changes were those renamings and preserves both checked versions. Original logs and hash records were retained; the original manifest's TripleDP hash is intentionally historical. Replay hashes are in `research/rmaf/results/triple-dp-verification-lean-replay-sha256.txt`.

The final fresh report check requested that README distinguish full-mode PASS from controls/pilot PASS; this wording was corrected. Its original MEDIUM recommendations were resolved. The source snapshot filenames are retained evidence, not alternative production modules.


## Receipt location correction

The parent corrected result ownership to `research/rmaf/results/triple-dp-verification*`. All eight initially misplaced receipts were moved there without changing their bytes; `triple-dp-verification-migration.json` records old/new paths and SHA256 values. Links and replay commands were corrected. The initial harness is retained under `verification/archive/run_verification.initial.py` at its receipt-recorded hash. The current harness now derives RMAF_ROOT and the results directory explicitly, restricts outputs to that directory, and refuses to overwrite existing receipts. The n<=5 scientific receipt is unchanged.

## Supplemental six-leaf plan (before outputs)

`supplement-n6-plan.json` fixes source leaf sets abc and def. The complete domain is all 945 unordered rooted binary targets and all nine source-topology pairs, giving 8,505 comparisons and 212,625 monochromatic-partition checks. The combinatorial bad-color histogram is fixed at 945 with none, 3,780 with one, and 3,780 with two. The pilot uses 40 uniformly sampled enumeration indices with seed 140626. A measured full-run projection below 60 seconds permits exhaustive execution; otherwise the fallback is a deterministic 200-case sample with seed 2140626. Three hand controls have exact optima 2, 3, 4 and additional cuts 0, 1, 2; a deliberately unsplit two-bad-triple mutant must fail, with the four-component hand solution as its clean twin. These expectations were fixed before any n=6 oracle run. This extension tests interactions between two bad colors on six leaves and makes no universal correctness claim.

The six-leaf pilot passed 40 comparisons and 1,000 partition checks, including 18 cases with two bad source colors. The timed comparison loop took 0.015016207998996833 seconds, excluding setup and controls. Its linear full-run projection is 3.1928212257867017 seconds for the same six-leaf distribution, below the predeclared 60-second threshold. All three new hand controls passed, the unsplit two-bad-triple mutant failed, and its clean twin passed. The complete 8,505-case run is therefore selected without altering the plan or reference implementation.

## Supplemental six-leaf result

The full supplemental run passed 8,505/8,505 solver comparisons and 212,625/212,625 characterization partitions. The bad-color histogram matched the predeclared counts: 945 cases with zero, 3,780 with one, and 3,780 with two bad triples. The comparison loop took 3.1542186250007944 seconds; total run time was 3.1597127909990377 seconds. Both source and target vertex disjointness were checked directly for returned partitions. The oracle, plan, script, and solver hashes are recorded in `research/rmaf/results/triple-dp-verification-n6-full.json`; the n<=5 receipt remains byte-for-byte unchanged after relocation. The tested fixed two-triple domain resolves the stated absence of any two-bad-triple examples in the earlier corpus, while arbitrary larger inputs and the universal graph correspondence remain unproved.


## Proof-scope review

The independent review of PROOF.md is retained in `referee_sim_PROOF.md`, with a pinned source snapshot and source/receipt locators. It found no HIGH-severity claim of universal graph correctness or a new global bound, and identified three MEDIUM clarifications: live versus full component counts after singleton removal, a canonical trimmed region normal form before claiming a bijection, and separate attribution of the 28 route theorem audits versus this verifier’s 19 core replays. The proof was not edited. The baseline Rule4 example was checked against its local source prerequisites and Figure 16 priority order; exact post-hoc checks confirm t=2 for all four cherries, the stated child, and the paid-cut arithmetic. These source-informed examples are not fresh acceptance data.

The corrected receipt path code passed an outside-directory refusal, an overwrite refusal, and a clean control replay. `research/rmaf/results/triple-dp-verification-path-controls.json` also confirms that the original n<=5 full receipt retained its migration-recorded SHA256.


## Shared-domain clarification

The independently generated n<=5 and fixed-two-triple n=6 domains overlap the route author’s prior census. The fresh oracle code and its output values did not feed production development, but these are not previously untested inputs. The correct claim is independent replication on a shared finite domain. The frozen supplemental script header’s word “held-out” refers to its new reference outputs and must not be read as an input-holdout claim; the script is retained unchanged at its pre-run hash. This clarification changes no test result or acceptance boundary.

## Connected-region follow-up

A fresh replay of `ConnectedRegions.lean` rebuilt the pinned TripleDP dependency in `verification/connected_replay/deps` and compiled all eight new supporting theorems. It rechecked 19 dependency theorem audits and a separate fresh positive-control theorem. The negative file failed specifically at its false omitted-path-vertex assertion, while the clean twin compiled. Total elapsed time was 1.4373423340002773 seconds. The source/command/log/axiom receipt is `research/rmaf/results/triple-dp-verification-connected.json`; the scope review is `research/rmaf/results/triple-dp-verification-connected-scope.md`. Source files and the original 28-theorem route receipt were not modified. The new result covers one root-containing path-convex address region; labelled region families, costs, and the complete G2 correspondence remain OPEN.

## Connected-region workspace-wrapper replay

The original direct-toolchain receipt and logs are preserved. The same source snapshots, theorem checks, false-path-vertex control, and clean twin were replayed using `/Users/paurel/Documents/ChatGPT/bootscience/bootloops-lean`, with ELAN_HOME set to `/Users/paurel/Documents/ChatGPT/bootscience/.runtime/elan`. Lean reported version 4.35.0. The launcher changed; scientific sources and checks did not. Separate receipt/log/build-output paths preserve the first replay.

The wrapper replay passed all eight extension and 19 dependency audits; the false proposition failed at `decide`, and the same clean twin compiled. Runtime for the four builds was 1.5432849589997204 seconds. `research/rmaf/results/triple-dp-verification-connected-wrapper.json` records the wrapper hash, explicit environment, commands, all audit names, and preservation hashes. `triple-dp-verification-connected-wrapper-comparison.json` confirms identical theorem/axiom audit lists, return codes, source hashes, and clean-control contents against the prior replay. G2 family/cost correspondence remains OPEN.
