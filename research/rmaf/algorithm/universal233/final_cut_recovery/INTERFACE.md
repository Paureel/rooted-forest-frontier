# Final cut recovery interface

This author package proves an executable final-certificate extraction in the actual ordinary rooted-MAF model. Fresh nonauthor proof/interface and source-cost acceptance is pending. The complete solver, global runtime, and novelty milestones remain OPEN.

`recover S P` checks distinct original source labels, the actual `partitionCheck (leaves S) P`, and actual `pairwiseEmbeddings S P`. It then calls the unchanged `CoreProgram.generate S (blockColor P) (P.length-1)` and returns its literal first output. It never enumerates set partitions or combines local cut sets. `blockColor` scans input blocks and returns the first label of the containing block.

| Declaration | Actual hypotheses | Conclusion |
|---|---|---|
| `BlockColors.checked_rank` | literal original source `partitionCheck` | realized color rank equals P.length |
| `BlockColors.checked_separation` | literal original source `partitionCheck`, b in P | b is exactly its original-label color class |
| `Permutations.checked_block_permutation` | P/Q checked on the same original S; Q monochromatic; Q.length=P.length | outer block permutation after individual label permutations |
| `Permutations.agreement_block_permutation` | proved `BlockPermutation P Q` | actual `agreement T S P = agreement T S Q` on the original trees |
| `Recovery.recover_checked` | source leaves Nodup; actual partition and embeddings | executable return; literal generator list=[o]; exact original cut cost P.length-1; exact block count; original realization; block/label permutation; actual output partition checker |
| `Recovery.recover_sound` | literal `recover S P = some o` | the same returned original certificate satisfies realization, exact cost, permutation and checked-partition conclusions |
| `Recovery.recover_edges` | literal returned output | distinct original valid cut addresses, each nonroot |
| `Recovery.recover_original_agreement` | original S leaves Nodup; actual original `agreement T S P` | returned literal partition remains agreement on T,S, with same cost and original realization |
| `Recovery.recover_success_iff` | none | success iff every explicit input check passes |
| `Recovery.accepted_guards` | literal successful output | source distinctness; P.flatten Nodup; nonempty blocks; each source label occurs exactly once; no absent label; source embeddings pass |
| `FinalWork.meterRecover_value` | none | exact value projection to `recover` |
| `FinalWork.meterColor_value/work`, `total_color_work` | none | executable color value and full scan charge, including skipped prefixes of the block list |
| `FinalWork.final_work_bound` | actual distinct source / partition / embeddings checks | full-source charge <= finalPolynomial(S,P)*2^(P.length-1) |
| `FinalWork.final_work_actual_cost` | same checks | exponent equals the returned original cut cost |
| `FinalWork.final_work_absorbed` | same checks; P.length-1<=q; rational c>=2 | additive final charge <= finalPolynomial(S,P)*c^q |

The table uses filename prefixes for navigation; declarations live in `Universal233.FinalCutRecovery`. Lean prints the exact declaration types in each source-bound receipt's `Interfaces.log`.

`BlockPermutation P Q` means there is a map f such that `(Q.map f).Perm P` and every f(b) is an actual `List.Perm` of b. Thus output order and within-block label order are the only freedoms. Original cut addresses remain literal generator addresses. Neither original-cut realization nor rank uniqueness is an assumed field: both enter through completed actual-source theorems and the new proved coloring bridge.

`CutRealization.RealizedOutput S o` includes original valid nonroot distinct cuts; a component list in output order with roots equal to cuts followed by the original root; exact residual-walk leaf sets; distinct complete components covering all original vertices; pairwise-separated component roots; a leaf in every original residual component; and block count equal to cut count plus one. These quantified vertices include suppressed paths. This package preserves that proposition and adds exact equivalence to P.

The work theorem composes the completed all-prefix core envelope, not a minimum-output-only path. Its source-operation interpretation retains the helper-versus-fine-operation qualification in COST-MODEL.md. Ordinary scalar comparison is parameterized by original-label and counter bit lengths. The final call occurs once after selection of P. No theorem here pays for searching for P or selecting a minimum.
