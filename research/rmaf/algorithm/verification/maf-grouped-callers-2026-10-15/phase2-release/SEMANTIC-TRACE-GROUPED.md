# Grouped forest reconstruction: nonauthor semantic trace

Reviewed the root-released FOREST-GROUPS-MANIFEST-v2 stack and its exact dependencies. Forward/reverse reconstruction is universal under its stated premises. The B query interface is conditional on a child-specific contract.

## Literal current forest state

`ForestState.proper` checks distinct target labels and that the leaf lists of the CURRENT whole source trees partition those target labels. `agrees` additionally checks the output partition, containment of every block in some whole current source, actual target embedding disjointness, and proper topology/embedding checks for each source's own block family. `additionalCost ss F` is F.length-ss.length.

`localTarget T U` is the literal target restriction. `owned ss U` FILTERS the whole current source list by full leaf containment in U. It neither cuts a source nor replaces a group by a free original-parent tree. `Owns ss Q` ensures that every current whole source has an owner. Checked nonempty Q and source partitions make that owner unique, even though filtering is expressed by values rather than occurrence indices.

`CrossClear T ss Q` compares actual target hulls of current source PIECES belonging to DIFFERENT groups. It permits overlapping target hulls among pieces in the same group. It does not require whole-Q hull disjointness, original-parent hull disjointness, or agreement between target and a free replacement whole-parent tree. The definition quantifies only owned pieces; ownership is a separate premise. This separation caused the retained frozen reference mismatch below.

## Forward and reverse proofs

`state_refines` obtains F-refines-Q from each block's actual source containment and source ownership. `local_forward` transports the actual target restriction and the source family, using `family_nested` and the whole-source containment in U. Forward decomposition needs no cross-clear premise; an already valid global agreement contains the required embedding facts.

Reverse reconstruction assumes proper whole state, checked Q, Owns, CrossClear, and actual local agreements for EVERY U∈Q. Checked nonempty groups and local partitions assemble the global label partition. Within-group target block hulls are transported back to the original target. Each block is contained in its actual owning current source. Hull monotonicity places that block hull within the owning source-piece hull, so CrossClear establishes all cross-group block pairs. This is exactly the needed target embedding argument; local agreement alone is insufficient.

For source checks, unique Q ownership and nonempty block partitions prove that filtering the concatenated output back to a given source gives precisely its owner's local family. Thus source topology and embeddings transport from the actual local source state. In the none-target case properness and checked Q force ss=[] and Q=[]; there is no invented empty leafless Tree. A missing C uses the separately proved two-group boundary [A,B], rather than adding a forbidden empty Q block.

The cost proof does not cancel truncated Nat subtractions without hypotheses. `source_blocks_balance` first proves sum_s(|family_s F|-1)+|ss|=|F| from actual agreement and nonempty source families, hence |ss|≤|F|. `source_group_lengths` proves that the total number of owned source occurrences is exactly |ss|. `sum_sub_balance` requires each local block count to be at least its owned source count, supplied by local agreement. Forward and reverse exact cost identities, and every-budget equivalences, follow. Reverse exact COST needs no CrossClear; global agreement in `reverse_every_budget` also needs reverse reconstruction's CrossClear premise.

## Actual frozen controls and qualification

The root fixture retains sources `(0,(1,2)), (3,5), (4,6), 7` and target `((((0,1),2),((3,4),(5,6))),7)`. The two B source-piece hulls overlap in the target. The supplied singleton B completion is valid with additional2. A valid A cost1 forest and C cost0 forest give seven final blocks/four current sources and additional3. A cheaper valid B completion `[[3],[5],[4,6]]` costs1, so the supplied cost2 result is explicitly not claimed minimum. The new `FreshConsumer.any_actual_B` consumes the universal theorem for ANY valid B forest on the actual two B source pieces. Its graph-clearance premise is derived from actual finite hull checks. `literal_root` checks the within-B overlap and exact total cost.

Actual readout reproduces 98 of the 99 strict frozen grouped comparisons. The remaining comparison is a defect of the frozen reference, retained unchanged in `algorithm-maf-grouped-fresh-review-groups-readout-v1.json` with FAIL status. For target `((0,1),(2,3))`, current sources `[(0,2),1,3]` and Q=`[[0,1],[2,3]]`, the reference expected CrossClear=false because source (0,2) is unowned. The actual definition has owned index lists [[1],[2]]; the unowned source is outside its quantifiers, while the two owned singleton hulls are clear. Actual CrossClear=true, Owns=false, and both local states are invalid. Therefore the universal reverse theorem cannot fire. The candidate definition/proof is consistent; the reference overstrengthened a predicate outside the theorem domain. No expectation or author source was changed. This is NOT an all-frozen-controls-pass result. The separate reference qualification, explicit false proposition for the incorrect expectation, and true twin bind this diagnosis.

The other cases include no target/empty forest, singleton, absent C, arbitrary ordering, overlapping whole-group hulls with clear current pieces, cross-group overlap with invalid concatenation, a more-refined valid output on the same pieces, and failed ownership/properness. A failed sufficient premise does not force every possible output to be invalid.

## Exact child contract

`ResidualSolverContract solve TB bs q` is guarded by proper TB bs. It states that `none` is equivalent to every valid local forest costing MORE than q, and every `some FB` is valid and costs at most q. It is a FEASIBILITY contract for the whole CURRENT B source forest at the specified target and budget. It is neither an attained-minimum contract nor an implementation.

`residual_query_lift` requires q>0, actual A cost1 and C cost0 agreements, proper whole state, checked [A,B,C], source ownership, piecewise PriorityClear, a contract for EXACT `(localTarget T B, bs, q-1)`, and an actual successful query at that same input. It derives the child properness and uses contract soundness, then the retained-A reconstruction and exact cost1+B identity. `residual_query_complete` uses the contract's none-completeness clause to exclude none given a valid child witness within budget. No contract, recursive termination or call implementation is constructed by either theorem.

`FreshConsumer.conditional_exact_child` consumes this exact interface while keeping IH explicit. `FreshChild` executes the frozen four-label child table against actual `ForestState.agrees`: all15 partitions match the independent graph checker, minimum1, and frozen budget0/1/2 feasibility and literal returned witnesses match. A new positive theorem proves that constant-none cannot provide the actual child contract at budget1. This remains a finite control, not a solver. Two own harness errors before this successful readout are retained: canonical partition order versus literal return order, then an output-prefix placeholder collision. Literal frozen returns were separately executed, never reordered or changed.

## Scope

This interface reconstructs grouped agreements and costs while allowing within-B overlap. It supplies no full recursive ForestState solver, global rule dispatcher, final original cut union/recovery or machine runtime. The one frozen reference mismatch and own harness provenance qualify the review. All three main milestones remain OPEN; same lineage, zero added replications.
