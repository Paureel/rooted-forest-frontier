# Rooted MAF — independent decomposition route

Status: OPEN. Read shared spec before other route material. No other route's journal or implementation consulted.

## Target and conventions
Target: exact ordinary rooted MAF, parameter optimum number of components; root augmentation conventions to be pinned from full text.

## Frozen controls
Pending independent oracle with hand-specified valid/invalid forests and known optimum pairs.

## Source reading receipts
Pending full-text baseline and primary kernel paper.

## Formulation A: common pendant subtree / shared cluster contraction
Pending precise formulation and counterexample search.

## Formulation B: disjoint component decomposition
Pending precise formulation and counterexample search.

## Exact experiments and timing
Pending pilot; no runtime projected before measurement.

## Lean lemma
Pending; no unproved assumptions claimed established.

## Interface and missing lemma
No improved base claimed. Kernelization alone is not a base improvement.

### Source receipt 1 — read
Baseline arXiv:2409.18634 v2 (21 March 2026), Section 2 pp.4–5, conditions (1),(2) and footnote2: forests are partitions with rooted homeomorphism and vertex-disjoint embeddings; baseline does not add rho but states algorithm works either way. Section4.1 Lemmas1–2 pp.7–9 defines splitting cores and shows factor2 splitting; Section4.2 pp.9–10 independently combines disjoint tree-forest subinstances. This is retrieval, not new discovery. Section6 Case3.1 pp.20–22 explicitly uses an attachment marker to distinguish whether an optimum component can extend beyond a common split, motivating a boundary-state test.

### Source receipt 2 — read
Kelk/Linz/Meuwese accepted-author PDF https://simonelinz.wordpress.com/wp-content/uploads/2022/10/klm22.pdf, Section5 pp.5–6, chain and 3–2-chain definitions/Lemma5.1; Section6 Theorem6.2: subtree/chain/3–2-chain irreducible trees have at most9 d−3 leaves in rSPR distance d. Root augmentation and d=components−1 must be handled before translating to the baseline convention. Full theorem proof pp.6–8 remains pending; not independently reproduced here.

### Instrument decision — before code
The BootLoops tools index was searched for tree-partition enumeration/phylogenetic combinatorial optimization. No indexed package supplies a rooted agreement-forest oracle: JaCK & Jill covers Bayesian phylogenetic evidence, not MAF. A new, independently written problem-specific partition/span enumerator is needed. It is experimental infrastructure, not a certified toolkit instrument.

### Frozen battery
controls.json written before oracle code or experiment. Four constructed controls: equal trees k1; conflicting rooted triplet k2; crossing span partition rejected; missing leaf rejected. Two candidate statements are frozen before search. Real progress unit is exact tree pairs/candidate instances checked, retained in results JSON. First experiment is a measured five-label pilot.

### Pilot receipt — executed
Command: `./bootloops-python research/rmaf/decomposition/search.py --limit 100`.
Output: `controls PASS 10; rooted five-label trees 105`.
100 pairs in0.015822 s; 38 cluster candidates,26 chain candidates. Linear100-pair pilot projection for5565 pairs is approximately0.881 s under unchanged five-label distribution; caching means this projection is only exploratory. Full run authorized, no long compute needed. One exact cluster-additivity killer retained in results before further search.

### Full five-label receipt — executed
`./bootloops-python research/rmaf/decomposition/search.py`: 5565 unordered pairs (including equal pairs),2250 common-cluster instances,1260 common3-chain instances. All10 frozen checks passed. Runtime0.365645 s first full run,0.461766 s replay after result-path preservation fix. Naive cluster additivity REFUTED: T=[a,[b,[c,[d,e]]]], T'=[a,[e,[d,[b,c]]]], C={b,c,d,e}, Kfull=3, Kinside=2, Kcollapsed=1, predicted2. Retained minimum forest {a},{b,c},{d,e}. Mechanism: no optimum local component has the correct attachment root available. Chain shortening top leaf has NO-FIRE on this finite domain, remains OPEN.

### Six-label pilot receipt and continuation
`--labels abcdef --candidate-only --limit 1000`: 1000 pairs,385 clusters,198 chains,10 controlsPASS,0.182258 s. Projection for446985 pairs is81.47 s at pilot rate, assuming comparable six-label distribution; rate may change with family. Continuing exhaustive six-label pair screening, evaluating optimum only where one frozen candidate applies. Results file named by size/scope so previous evidence remains retained. Initial result-path refactor had a NameError; corrected before replay; no scientific state accepted from failed run.

### Kernel proof reading completed — retrieval
Read accepted author manuscript Section6 Theorem6.2 proof (PDFp.6) in session. Counting generator sides gives9 d−3 after three prescribed reductions. This is a retrieved theorem, not a new or independently Lean-verified result. Section7 (PDFp.8) concerns ACYCLIC MAF/minimum hybridization and uses weighted2-chains; that does not license unweighted2-chain reduction in this ordinary MAF task.

### Lean support draft
IndependentMinima.lean is a Std-only generic theorem: attained minima of two independent certificate spaces compose additively. It neither encodes rooted trees nor assumes the missing MAF gluing statement has been proven. Actual structural certificate correspondence is still OPEN. Parent handles Lean runtime setup; compilation/axiom audit pending.

### Two-state repair — screened, not proved
Frozen in boundary-pin.json before implementation. For common pendant cluster C let A=inside optimum, A_aug=inside with root attachment marker, B=outside restriction optimum, B_collapsed=outside with cluster marker. Candidate identity K=min(A+B,A_aug+B_collapsed−1). All2250 five-label cluster cases: NO-FIRE,0.110711 s. State counts1470(0,0),720(0,1),60(1,0) for marker penalties. Killer of naive formula has A2,A_aug3,B1,B_collapsed1; repaired formula gives3. Missing step is universal certificate gluing/restriction correspondence with marker attachment state, not scalar arithmetic. This approach may be existing structural theory; no novelty claimed.

### Six-label receipt
446985 unordered pairs screened,153090 cluster instances,55800 chain instances,10 controlsPASS,42.192957 s. Chain shortening remainsOPEN despite no fire.

### Targeted seven-label common-chain family pilot
210 trees constructed with chain(a,b,c) fixed, all distributions/topologies of d,e,f,g below versus above it.100 pairpilot0.108564 s, maxKseen4. Same-family full22155 pairs estimated24.05 s under pilot cost; running bounded complete family. Exact optima require larger partitions than prior six-label run; independent timing recorded.

### Theory-finding transition
Both scalar cluster additivity and unweighted3→2-chain shortening were killed by exact witnesses. Switched to mechanically enumerating64 penalty tables over three reduced-forest states: a,b together; both singleton; mixed. First frozen corpus1260 five-label chain cases plus seven-label killer yields12 surviving tables in0.177066 s. The state penalty(0,1,excluded) survives; this is a search output, not a general theorem. Extend the corpus with all fixed-chain seven-label family pairs and seeded eight-label samples after a100 sample pilot. No narrative rescue of dead unweighted claim.

### Eight-label pilot
100 seeded eight-label samples plus1261 frozen corpus rows:1.190762 s,12 penalty tables remain. Seed20261014. Project2000 samples at approximately23.82 s conservatively using entire pilot runtime; all seven-label fixed-chain family adds22155 rows. Proceeding bounded extension, keeping size/scope-named files.

### Penalty synthesis extension — executed
Command `./bootloops-python research/rmaf/decomposition/penalty_synthesis.py --family --random-eight 2000`.
25416 rows,64 candidate tables,12 survivors,42.180688 s. Rows comprise1260 five-label instances+one retained7-label killer+22155 complete fixed-chain7-label pair instances+2000 seeded8-label samples. Surviving strongest table(0,excluded,excluded) corresponds to same-component constrained2-chain replacement. This is candidate OPEN, no universal proof. Missing lemma and explicit lifting/normalization/mark-propagation obligations in missing-lemma.md. Future experiment is two interacting common chains, not another scalar rephrasing of dead claims.

### Lean receipt — executed
Lean4.35.0 local runtime: `.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean research/rmaf/decomposition/IndependentMinima.lean` returned exit0.
`RMAF.Decomposition.independent_minima` axioms[propext].
`RMAF.Decomposition.hypothetical_two_leaf_side_count` axioms[propext,Quot.sound].
No sorry/admit/custom assumptions introduced. These are generic support theorems; they do not formalize MAF semantics or close a structural missing lemma.

### Current disposition
No global algorithm improvement established. Two natural unweighted/scalar formulations exactly refuted. Attachment-state cluster identity and marked2-chain replacement screened OPEN. Kernel-size arithmetic and Cartesian minima compose checked by Lean. Fresh independent verification and full semantic formalization still outstanding.
