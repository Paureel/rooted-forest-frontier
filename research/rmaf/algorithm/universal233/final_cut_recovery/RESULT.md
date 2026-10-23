# Final original-source cut recovery

The executable `recover S P` checks the original ordinary source S and literal partition P, calls the actual completed generator at budget P.length-1 with one distinct color per P block, and returns the literal output's original cut certificate. The author Lean proofs establish exact original realization, cost P.length-1, original agreement preservation, and the source-operation bound described below. Fresh nonauthor acceptance is pending. The complete solver, global faster-runtime proof and novelty milestones remain OPEN.

## Returned certificate

Input checks require distinct original source labels, actual `partitionCheck (leaves S) P`, and actual `pairwiseEmbeddings S P`. They reject absent/repeated labels, empty or overlapping blocks, repeated source labels, and source-embedding overlap. `recover_success_iff` proves success exactly when all checks pass.

The executable block scan uses each containing block's first label as its color. `checked_rank` derives that there are exactly P.length realized colors, and `checked_separation` derives that the original color classes are exactly the P blocks. These conclusions supply the hypotheses of the completed actual minimum-rank theorem. The actual budget-P.length-1 generator therefore returns one literal output, and `head?` obtains it without scanning any other partitions.

`recover_sound` proves the returned literal cuts and output partition satisfy `CutRealization.RealizedOutput` on the original S. This includes all original vertices on suppressed paths, exact component leaf sets, complete component coverage, no leafless components, distinct valid original nonroot cuts, separated component roots, and block count equal to cut count plus one. The new `BlockPermutation` conclusion identifies the component leaf sets with P using actual label and block permutations. The cut count is exactly P.length-1.

`recover_original_agreement` takes actual original `agreement T S P` for an arbitrary original target T. It proves actual `agreement T S o.partition` for the returned output o, with unchanged component/cut cost. The transport proof checks literal restriction, rooted spans, minimal embeddings, pairwise embeddings and partition checks under label/block permutations. It assumes no cut-subset relation, local-cut union, or prototype cut-choice identity.

## Work

The final recovery is called once after selecting the final minimum labelled agreement. `meterRecover_value` proves its exact value projection. `meterColor_value/work` and `total_color_work` pay the literal block scans at every original leaf. `final_work_bound` adds these to the completed full generator envelope, preserving all refused/pruned prefixes and actual receipt append work. The result is

    work <= F(S,P) * 2^(P.length-1),
    F=guardCharge+colorCharge+initialCharge+1+2*(cap(inputResource)+6)*P.length.

For checked input with n leaves and maximum original-label bit length L, F is O((n+1)^8), and direct integer encodings give bit cost O((L+n+1)(n+1)^8 2^(P.length-1)+input_encoding_length). `final_work_actual_cost` uses the returned original cut count as the exponent. `final_work_absorbed` proves the rational c>=2, P.length-1<=q consequence F*c^q, and `Regression.final_work_233` consumes it at c=233/100.

The source-operation correspondence for guard and helper implementation is the conservative mathematical argument in COST-MODEL.md. Lean checks value/color/size/envelope algebra; it does not certify an extracted machine-instruction trace. Fresh nonauthor source-cost review must check this correspondence.

## Evidence

The pinned actual controls ran before universal proof construction. The preserved receipt `results/algorithm-universal233-final-cuts-controls-20261015T104115Z` contains eleven passing literal control statements and three rejected false propositions. Controls include arbitrary original labels and reordered labels/blocks, a suppressed-path example with original addresses, all singleton cost, root refusal, invalid label partitions and overlapping source embeddings, and an incorrect concrete cut-list witness.

The canonical full source replay and declaration audit are named in LATEST-REPLAY.txt after successful completion. Finite controls and author replay are development evidence. Independent nonauthor acceptance remains separate.

Canonical author receipt: `results/algorithm-universal233-final-cuts-replay-20261015T105812Z`. It rebuilt 62 exact source modules, audited 2719 declarations by full actual module origin, and observed only Classical.choice, Quot.sound, propext. All four false propositions were rejected; missing-record, private custom-axiom, and source-pin corruption plants were caught. Positive source compilation took 32.843171 seconds on this host. The scoped `./bootloops-check emitall --par 1` selftest passed; no unrelated full toolkit suite or external engine was run.
