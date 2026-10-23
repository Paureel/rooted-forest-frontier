# Actual source generator coverage and raw mass

The exact `CoreProgram.generate` has a finite-budget original-partition refinement theorem and a universal raw rational-mass theorem. The full faster rooted-MAF algorithm remains OPEN. This package contains author kernel checks; fresh nonauthor verification and the remaining algorithm interfaces require separate review. Ordinary rooted cost is components minus one, with no added root label.

## Original partition coverage

`OutputBudget.generate_partition_coverage_paid` takes the following input facts directly:

- the original source tree T has distinct leaf labels;
- `RMAF.partitionCheck (RMAF.leaves T) bs = true`;
- `RMAF.pairwiseEmbeddings T bs = true`;
- each original block in bs is monochromatic for the supplied original-label coloring;
- the requested cut budget q is at least `bs.length - 1`.

The theorem produces a member o of the literal list `(CoreProgram.generate T color q).outputs`. Every original block b in bs is contained in a single block of `o.partition`, and `o.sourceCuts.length <= q`. Taking q equal to `bs.length - 1` gives the requested ordinary budget. The original bs remains in the conclusion after every homogeneous contraction. The theorem makes no edge-subset claim.

The proof starts from the frozen executable-check-to-source construction. `FullTransport.normalize_full_transport` strengthens normalization transport by proving that every normalized group occurrence has an old occurrence mapping to it. `Coverage.fullTransport_ownerCover` maps a finite list covering all source-owner IDs to a list of equal length. `Coverage.filter_owner_decreases` strictly shortens this list at each chosen source singleton. `Coverage.erase_refines` reconstructs all labels belonging to the detached singleton owner and carries each other original owner to its surviving suppressed-graph occurrence.

`Coverage.run_coverage` inducts on the actual run budget. Its zero-budget continuation has no outputs; a nonempty suppressed source cannot have an empty owner cover, so the proof cannot treat pruning as emission. `Entrypoint.generate_partition_coverage` then consumes the original checks and the exact `min q (leafcount - 1)` cap. The cap inequality follows from `Entrypoint.partitionCheck_block_bound`, proved from the Boolean partition test.

## All emitted outputs and raw mass

Let r be the number of distinct original input colors, B be the actual capped budget, and cost(o) be `o.sourceCuts.length`.

`ColorBudget.generate_color_cost` proves `r <= cost(o) + 1` for every literal emitted output-list member. `OutputBudget.generate_output_budget` bounds every such recorded cost by the requested budget. `RationalMass.generate_output_cap` gives the sharper bound `cost(o) <= B` used when clearing denominators.

`RationalMass.generate_rawQ_mass` proves, for every rational c >= 2,

    sum over the literal output list of c^(-cost(o)) <= c^(1-r).

The definition `rawQMass` is exactly a `List.map` followed by `List.sum`; it retains duplicate entries. The theorem applies in particular to c = 233/100. `Controls.raw_mass_at_233` consumes that specialization for the mixed quartet.

The actual-program induction first proves the exact cleared inequality

    [sum c^(B-cost(o))] * c^(r-1) <= c^B.

A unique-color step has one child and can reduce the number of live colors by at most one. A two-child step comes from the actual chooser after its unique-color search returned none. `ColorSteps.choose_two_nonunique` extracts that fact, and `ColorSteps.erase_colorCount_two` proves that each of its actual erasures retains every live color. The two child contributions are bounded using 2 <= c. Empty output lists from original-root guards, duplicate-cut guards, whole-source guards, chooser refusals and budget pruning contribute zero in the actual recursion.

For a real c >= 2, the same mass inequality follows from the proved dyadic case and the proved cost lower bound. Put s = r-1. For each emitted output,

    c^(-cost) = 2^(-cost) * (2/c)^cost
               <= 2^(-cost) * (2/c)^s.

Summing the literal list gives at most `2^(-s) * (2/c)^s = c^(-s)`. This last real-number transfer is an ordinary scalar argument stated here; the Lean endpoint uses rational bases, including 2.33 exactly.

## Recorded cost and remaining interfaces

All cost and mass statements above use the actual recorded original cut addresses. The frozen cut-record theorem also proves those addresses are nonroot and unrepeated. Identifying the records with nonredundant original residual components remains a separate graph theorem. `FIRST-GAP.md` records its exact call site.

The frozen bound

    visited + childAttempts + 3 <= 3 * 2^(q+1)

counts recursive prefixes and attempted children, including prunes. It is exponential in q. It does not prove polynomial work per prefix. No polynomial implementation-work bound, global faster-algorithm bound below 2.3391, or novelty conclusion is claimed by this package.

## Evidence

`LATEST-REPLAY.txt` identifies the retained expanded replay. The replay copies every imported source module into an isolated local directory and compiles those copies using `./bootloops-lean`. It inventories every declaration by originating module, including compiler-private and generated declarations, and rejects dependencies on axioms outside `Classical.choice`, `propext`, and `Quot.sound`. Source hashes are checked against the frozen integration manifest before and after compilation.

The controls include a mixed cherry, a unique singleton, homogeneous contraction after a third-parent suppression, budget-zero pruning, the exact budget threshold, duplicate-input refusal, and literal output-list multiplicity. False budget-zero emission, false exact-partition preservation, and false deduplicated mass must be rejected. A true arithmetic proposition must compile, a false one must fail, an omitted audit record must be caught, and an unrelated custom axiom must be rejected. Failed development compiles and unsuccessful replay attempts are retained.

The proof author read and reused the frozen integration sources. These compiles and controls are author development evidence. They do not satisfy the prove-protocol requirement for fresh nonauthor reconstruction or establish novelty. No large census or raw-case dump was run for this package.
