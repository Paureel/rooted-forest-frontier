# Actual binary cheap continuation

Author kernel result; fresh nonauthor acceptance remains pending. All three main algorithm milestones remain OPEN. This package proves scoped graph and local-certificate facts for the both-bad binary-edge case. It does not prove a complete solver, global recurrence, compiled-machine runtime, or novelty.

The primary entry is `Universal233.BinaryCheap.selected_cheap_continuation` in `SelectedContinuation.lean`. Its original inputs are proper equal-label trees, the actual source checks for P=[A,B,C], original A/B disagreement, C agreement, the literal G-selected mutually-clear binary edge, C-versus-A/B clearance, and literal q3 A-clear probe acceptance. It assumes no cheap-output geometry, cost profile, sector rank, or paid residual query.

| Actual result | Declaration |
|---|---|
| Selected edge supplies both parents' nonempty sectors, mutual clearance and each parent's sector separation | `edge_facts` |
| A-clear color has exact original input rank four | `cheap_rank` |
| Accepted q3 output is the same singleton at every q≥3, costs three, and contains full input color classes | `accepted_cheap` |
| Singleton classes are exactly [A_yes,A_no,B,C] up to block and label order; actual source partition/embeddings and actual target embeddings pass | `selected_accepted_partition` |
| Both good A sectors construct an actual agreement with two pieces on the exact original S\|A and T\|A | `local_cost_one` |
| Since original A is bad, actual DepthOne returns a globally minimum one-cut result with a literal original LOCAL source-cut certificate | `cheap_good_sectors_pretest` |
| Every actual opposite-core output keeps whole A/C, the identical local problem/certificate, parent refinement and A/Bpiece/C cross-clearance | `every_opposite_output`; `OppositeSafe` in `selected_cheap_continuation` |
| If either A sector is bad, the actual cheap output has two distinct bad target-disjoint blocks | `cheap_two_bad`; `TwoBad` in `selected_cheap_continuation` |
| Swapping A/B preserves the same actual selected edge and valid source P | `selected_symmetry` |
| Two literal q3 failures force every output of both actual cores to cost at least four and bound their appended raw LIST mass by 4*c^-4 for rational c≥2 | `selected_two_high` |

For exact B-cheap symmetry, apply `selected_symmetry S T A B C e` to derive the three source/selector premises, then apply `selected_cheap_continuation S T B A C e`. The printed cheap partition is [B_yes,B_no,A,C], and the opposite core retains B/C and the original local B certificate. Both applications use the same original edge e.

`SameMembers` states equality of full original-label membership. Both actual and canonical partitions pass literal nonempty/count/source checks; label order and block order carry no graph meaning. `OppositeSafe` proves clearance between groups. It permits overlap between B pieces and makes no assertion that an arbitrary opposite-core output is already an agreement forest.

A local certificate is measured on the original restricted A tree, including its literal local address. Mapping that address into the whole original S and combining it with whole-source cuts remains a later obligation. The two-bad conclusion supplies an explicit query condition; positive own optimum alone supplies no such condition.

The new proofs compose completed frozen pair_assembly201, rank_dichotomy193, rank_consumer153, kept_parent228, depth_one317 and their original geometry/assembly sources as development inputs. They provide no independent acceptance of those inputs. The only new module adapter is filename `Restriction -> DepthRestriction` for DepthOne's original restriction lemmas, plus the first import in its `Embedding` copy. All proof bodies remain unchanged and both hashes are retained in `STACK-PINS.json` and the final certificate.
