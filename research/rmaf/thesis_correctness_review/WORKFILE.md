# Independent correctness review — 2026-10-14

Status: OPEN. Reviewer authored none of the target reconstruction. Independent phase excludes author SEMANTICS.md, ProtectedBranch.lean, results summary, algorithm.py, reference.py, and all complexity/transfer agent work.

## Target and permissible assumptions
The campaign spec requires ordinary rooted agreement forests with equal restrictions and vertex-disjoint minimal embeddings, k components, q=k−1 cuts; thesis rho convention must be kept explicit. Standard Lean axioms may be audited; published exchange lemmas remain conditional imports until formalized. Finite agreement cannot certify universal correctness.

## Source read ledger
Pending: primary source Chapter 2 rho convention; Chapter 6 definitions, Lemmas 6.3/6.5, branch rules, Theorem 6.12 and proof.

## Frozen independent controls
Pending source reading. Freeze controls and cut/partition representation before target files are opened. Positive/negative twins required, exact integer/set arithmetic only.

## Independent instrument and timing
Consulted bootloops/tools/README.md: no rooted tree agreement-forest verifier exists there. A one-shot fresh enumerator is justified for independent adversarial review; it must not import campaign oracle/helper code. Pilot at two bounded sizes; record runtimes before larger enumeration.

## Independent source-semantic audit
Pending: source branches; protection coupling; contraction; depth; root-safe common cherries. Distinguish literal source-domain omissions from algorithm refutations.

## Target interface audit
Pending until independent controls exist. Trace every proof use-site and check delivered hypotheses.

## Lean replay
Pending isolated clean-dependency replay of seven declared lemmas, axiom audit, passing true twin and rejection of a mathematically false twin.

## Findings and delivery scope
Pending executed evidence. Full universal correctness remains OPEN unless completely proved. Retain source and frozen results untouched; local output only.

### Source reading checkpoint 1 (before target read)
READ: thesis text PDF p25 / printed p12 adds a labelled unary root rho to X (lines 820–828). Printed pp104–105 (PDF117–118) describe active Rt blocks, done roots, common sibling contraction and AC/B/ABC; printed p107/PDF120 specifies root-sibling cut exclusion and OR inheritance when edges suppress. A2BC has a separate ec-protected branch (B before A), while A3BC has A/B/C order. Printed pp114–116/PDF127–129 proves Theorem6.12 by a leftmost promising path in an unprotected variant; its claimed subtree relationship needs control of protection-dependent branch choice/order. This last statement is an inference about a proof obligation, not a refutation.

READ: Lemma6.3 printed p101/PDF114 requires triples AND nonoverlap. Lemma6.5 printed pp101–103/PDF114–116 has F1 forest of T1, F2 forest of T2, E a successful completion, and E2 subset E making (a,c) common siblings; replaces a–c path cuts by none if ≤1 or the LCA parent edge if ≥2. The latter parent edge needs existence or an explicit root-safe interpretation. Its actual uses in Lemma6.10 pp112–113 and Theorem6.12 p116 must be checked; undefined root-general formulation alone does not kill those uses.

### Independent pilot and source checkpoint 2
The source PDF printed p110/PDF123 was rendered and inspected because the supplied text skips its prose. BCY makes B then CY; depth (i) restricts to descendants of the deepest parent of a protected edge of F1, (ii) maximizes F1 depth among eligible pairs, (iii) uses separate F2 components / deepest F2 member as tie priorities. Rt stores common subtree roots; depth is in the unsuppressed rooted forest representation after ordinary cuts, not simply in a tree where every Rt subtree has been replaced by a new leaf.

Frozen controls were written and sha256-pinned before target artifacts were opened. Independent graph code uses labelled unary rho, not a new rho leaf, and imports only Python standard modules. Cut enumeration uses component recursion after deleting edges; partition enumeration independently uses paths, restrictions, and vertex-disjoint embeddings. Deepest shared layer: input parent/child graph and mathematical AF convention. These routes can share representation bugs; by-construction crossing/rotation/root controls probe this risk, and this is finite corroboration rather than universal proof.

Executed pilot: 14/14 controls passed, including corrupted expectation, overlap-omission, and OR-overwrite mutants. For labelled rho with 3 ordinary leaves, 9/9 ordered tree pairs passed cut/partition equality in 0.00176 s; with 4 leaves, 225/225 pairs in 0.1303 s and 144 A2BC exchange premises survived. Both measured sizes use identical exact code. Full frozen scope repeats these regimes and adds unaugmented n=3,4; projected runtime <1 s from the measured largest slice, assuming no harder than labelled rho with the same ordinary leaves. No long run needed.

Independent phase complete: fresh controls, cut/partition route, source branch table, root-safe fixture, and timing evidence exist before author file access. Now beginning target semantic/interface audit. Results from this point may inspect author artifacts and cannot be relabelled as blinded construction.

### Target audit checkpoint 1
Opened SEMANTICS.md, ProtectedBranch.lean and summary only after independent phase. Seven Lean statements are local logic/Boolean/cardinality theorems with explicit hypotheses, not graph AF theorems. Concrete concern to test: `Cover` universally quantifies over EVERY optimal original-edge cutset, while source Lemma6.8 is an existential optimum-preserving branch assertion. Edge-shift equivalences may violate the universal predicate even when the algorithm is correct. Test frozen graph enumerator before drawing a conclusion; possible downgrade is a normalized optimal family or weaker existential branch theorem.

### Lean replay and candidate pilot
Isolated replay from `lean-isolated/` with `LEAN_PATH` unset succeeds for all seven unmodified statements. Printed union is exactly propext, Quot.sound; four branch theorems have no axioms. Original false arithmetic control fails specifically because `decide` proves 1≤0 false; positive twin 0+1−1+0≤0 and negation of the false twin both pass. Three additional review-only existential-interface lemmas compile with no axioms. They repair the quantifier logic only; no AF graph premise is proved.

Candidate pilot against the frozen independent partition oracle: 225 four-leaf pairs / 939 budgets in 0.2294 s, 10 five-leaf pairs /49 budgets in 0.0315 s, 10 six-leaf pairs /51 budgets in 0.0833 s, zero failures. Projected 150 five-leaf and 150 six-leaf fresh pairs plus nine author-selected branch examples <3 s from same-size pilots; larger run remains finite evidence only.

### Concrete findings
1. `Cover` is false for all raw minimum original-edge cutsets. Fresh exact witness: T1=rho→(a,(b,(c,d))), T2=rho→(((a,c),b),d); selected sibling pair (c,d), pendants a,b. Optimum is q=2. Cut the incoming edge of cluster {a,c} and leaf a: the AF is {a},{c},{rho,b,d}, so no endpoint edge (c or d) and not both pendant edges (a,b) is cut. The branch predicate is false on this optimum. This is an actual A2BC initial-state shape; algorithm decisions still agree. `cover-adversary.json` retains 36 local cherry-state counterexamples. The printed source Lemma6.8 asserts existence of an optimum-preserving branch; it does not supply universal raw-cutset Cover. Either prove normalization into a restricted optimal family or use existence-of-covered-optimum plus child-membership exclusion. Review-only ExistentialRepair.lean checks the latter logical repair.

2. A second exact source-domain witness shows that fixing only root-parent existence does not make standalone Lemma6.5 universal. T1=rho→((a,b),(c,d)), T2=F2=rho→((a,c),(b,d)); F1 has components (a,c), b, d, rho (a forest of T1). E={ea,ec}, E2=empty; all stated standalone hypotheses hold, the LCA parent exists, and E yields the AF {a},{c},{rho,b,d}. Proposed E0={e_LCA} yields (a,c) and {rho,b,d}, whose T1 embeddings overlap. This violates active F2-to-F1 component containment, so it is a source-domain omission, not an algorithm counterexample. Chapter2 p17 explicitly says algorithm states maintain containment; the repair must carry that hypothesis (or AF-of-F1 compatibility) into normalization. The clean twin with T1=T2 passes. Source read: Chapter2 pp15–18/PDF28–31, Lemma6.5 pp101–103/PDF114–116.

### Active-state audit pilot
The first pilot hit a reviewer harness bug (`frozenset.add`) before producing a result. Changed only the intermediate set to mutable; the rerun checked 10 actual candidate snapshots in 0.0927 s, eight nonvacuous normalization constructions, no normalization failures, and two further raw-Cover violations. A two-pendant positive/omitted-removal negative twin was added after this pilot; it is explicitly retrospective, not a frozen independent control. The original independent controls remain frozen and unchanged. Projected 120 snapshots ~1.2 s at this measured rate; allow 20 s because state shape distribution can change. No long computation needed.

### Final review checks
`finalize.py` verified all original frozen source hashes and the original 14,250-pair receipt denominators; those full author sweeps were inspected, not independently rerun. Fresh review counts are 534 candidate pairs /2,507 budgets, all nine branch variants, zero decision mismatches. Original four fixed optima, Lemma6.3's domain witness and the author's three-leaf root example were independently reconstructed. The 120-state audit checked 50 nonvacuous normalization constructions with zero failures; none required the root-safe parent omission. These limitations are explicit in the summary.

First prose pass checked scope, source attribution and all counts against JSON; second pass checked wording and exact line locators, correcting Cover use lines from 31/53 to 30/52. Pattern sweep found none of the selected hype/overclaim phrases. The fresh-context referee-sim table addresses the author target, with the raw-Cover impossibility as its main proof-interface objection. No claim of universal correctness, complexity improvement, convention transfer or novelty is made. User-facing dashboard status remains OPEN.
