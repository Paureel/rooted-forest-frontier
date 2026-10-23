# Preregistration v1 — sealed before first engine execution

Date: 2026-10-15. Stage: PRE-CANDIDATE. Root TARGET-v1 and public definitions/statements only. Candidate and prior verifier material remain sealed.

## Meaning and scope

The graph instrument is one-shot, original code. Original vertices are binary-child address tuples; parent edges are pairs of addresses. Minimal hulls consist of all paths joining a block's original leaves, rooted at their original LCA. Agreement means equal unordered suppressed restrictions per block and disjoint block hull vertices in BOTH original trees, with a proper same-label partition. Refinement is blockwise containment. No artificial rho. Original cost is number of final blocks minus one.

These semantics will be checked against the whitelisted public definitions before engine execution; any difference requires a separately frozen amendment, never silent tuning. Exact integer/rational controls use equality, not tolerance. Shared mathematical definitions are disclosed; this is no statistical replication.

## Hand-derived initial literal expectations (not yet executed)

S = (((0,2),1),(((3,5),4),(6,7))).
T = (((((0,3),1),4),(2,5)),(6,7)).
P = 012|345|67.

S leaf addresses: 0:000, 1:01, 2:001, 3:1000, 4:101, 5:1001, 6:110, 7:111.
T leaf addresses: 0:00000, 1:0001, 2:010, 3:00001, 4:001, 5:011, 6:10, 7:11.

Source hulls: A={0,00,000,001,01}; B={10,100,1000,1001,101}; C={11,110,111}. Pairwise disjoint.
Target hulls:
A={0,00,000,0000,00000,0001,01,010};
B={0,00,000,0000,00001,001,01,011};
C={1,10,11}.

A restriction S=((0,2),1), T=((0,1),2); B restriction S=((3,5),4), T=((3,4),5); C restriction identical (6,7). Thus A/B are bad and C is good. Target C clears A and B.
At edge child 000, endpoints 00 and 000 have union-hull degree 3; below sectors A={0,1}, B={3}, above sectors A={2}, B={4,5}. At edge child 0000, endpoints 000 and 0000 also have degree 3. The selector choice is PENDING public-definition check and is not assumed.

F=01|2|3|45|67 is an original AF. Expected 5 blocks; original cost4, additional cost2. Lower bound: A and B each need at least 2 blocks because their whole rooted restrictions disagree, plus C nonempty needs >=1, so any refiner has >=5 blocks. q3 fails, q4 has F. Expected independent finite refiner denominator: Bell(3)*Bell(3)*Bell(2)=50. No unrestricted 8-label partition census.

Expected source-only corruption: Fbad=03|1|2|4|5|67 violates refP and may serve only generic/source-vs-target checks; a refP both-crossing partition is 01|2|34|5|67 at edge000 and its target hulls overlap, so original AF must fail. The source partition P itself is source-valid but target restriction equality fails, hence is the clean source-only false agreement plant.

## Fixed manufactured truth controls

1. Identical quartet S=T=((10,20),(30,40)): whole-label block is AF cost0; each singleton is AF cost3; split12|34 is AF cost1; original hull disjointness checked on each case.
2. Quartet source ((10,20),(30,40)), target ((10,30),(20,40)): whole block fails shape. Source split10,20|30,40 fails target hull disjointness. Four singletons passes.
3. Empty block, duplicate label, absent label and incomplete partition each fail exact partition checks; arbitrary negative/nonconsecutive integer labels and child swaps preserve semantic values.
4. Initial literal fixture and both A/B orientations; input order/child swaps retain semantics while original addresses are recomputed explicitly, never reused blindly.

## Fixed finite-case obligation search (after pilot only)

No broad all-eight-leaf search. Generate a bounded bank from interleavings of two fixed 3-leaf or one fixed 4-leaf parent with source-disjoint C=(6,7) (or renamed labels), with exact cap registered before launch after pilot. Source-parent refiners are enumerated separately. Search purposes: genuine selected-edge regimes, sector-good/bad variants, both q3 probes failing, A-only/B-only crossing F, opposite-core internal-target-overlap occurrences. Finding controls is exploratory and must be followed by a second exact frozen bank amendment before those controls grade candidate behavior. Any unmet obligation remains pending.

## Raw and charged arithmetic controls

Let mass(ds,c)=sum(c^(-d)). Bound=4*c^(-4). Exact c controls: 2,233/100,3; out-of-domain4. Raw [3,4,4] has normalized mass c+2 and exceeds bound for c>2. Charged [3,5,5] has normalized mass c+2/c <=4 on [2,3]; [3] also <=4 there. At q5 literal charged budgets are [2,0,0]; at q4 prune [3,5,5] BEFORE Nat subtraction, retaining only budget1. These are abstract reference traces, not a claim about the starting tree. Exact proof for interval: c+2/c increases for c>=2 (or multiply to c²-4c+2<=0; convex quadratic maximum over [2,3] is <=0). c4 violates for [3,5,5].

Keep occurrence order and multiplicity. [] mass0; failure after call counts that call; duplicate calls count twice; early-stop trace ends at actual failure; failed original return checks discard result but preserve calls. Returned candidate is minimum number of blocks among every actual valid returned occurrence; tie policy must be checked against public statement or left unspecified.

## Detector plants and clean twins

Each plant is a separate deliberately corrupted ledger/input paired with an uncorrupted one. Expected failure location is preregistered: source-only agreement -> original target checker; selector/clearance omission -> theorem-premise checker (not inferred runtime refusal); dropped cover occurrence/different coverage-mass lists/favorable filtering -> ordered occurrence equality; duplicate/omitted charged call -> ordered trace equality; wrong q/additional budget/double-parent charge -> integer budget identity; subtraction before prune -> negative-budget guard; wrong callback target/source/free whole-B -> exact request tuple; local-to-whole cut union/own-minimum discount -> required-premise/interface field; hidden optimum -> declared runtime dependency field; uncharged prefix/refusal/append/materialization/checker/payload work -> work-component ledger.

Some of these are semantic ledger detectors before source release. They do not prove detection of arbitrary code defects; actual candidate adapters after RELEASE must use frozen exact source/type/body/import and compiled trace checks.

## Std-only full-origin toy gates

Audit all constants actually originating in every custom toy module, including private/generated constants and unused custom axioms. Read exact raw type/body and imports. Accept only standard axioms (propext, Classical.choice, Quot.sound); custom axioms fail even if not a queried theorem dependency. Register module source hashes and require exact one-to-one origin coverage. Tests: positive arithmetic truth and false twin (must fail Lean compile); unused custom axiom; private axiom/producer; generated equation/function body; missing/duplicate/wrong origin records; changed source/import/type/body adapter records. Every corruption must be caught. Audit compiler/library sources may be read as tooling APIs; no old verifier implementation may be read.

## Timing and acceptance

Plants first. First runtime unknown: measure one tiny manufactured control and one initial literal case, then use the same code/settings for pilot sizes 1 and 4. Bounded bank cap <=128 tree pairs and <=400 refiners per pair unless a new preregistration with measured projection is frozen. Intended run under 60s; if pilot projects >120s, restructure, do not broaden. Progress = checked control/tree rows on disk. Keep full outputs/failures/corrections. READY contains all source/control/output hashes and unresolved obligations. No self-release.
