# Remaining consumers after source-core realization

The source-core proof has passed the author source-bound kernel replay. Fresh hostile and nonauthor review are still required before treating it as accepted development input. The complete rooted-MAF algorithm below 2.3391 remains OPEN.

## Raw mass

The first mathematical consumer not proved in this package is a raw output-mass theorem for the exact frozen `CoreProgram.generate` output list, counting emitted occurrences with their actual nonredundant original-cut costs. In the notation of this package, the required form is

```
r := colorCount T color
sum over o in (generate T color q).outputs of c^(-o.sourceCuts.length)
    ≤ c^(1-r)
```

at the parent's pinned admissible base `c` and hypotheses. No mass inequality is assumed by `checked_source_core`, and no such inequality follows merely from the proved individual lower cost. `generate_realized_color_cost` supplies the individual `cost ≥ r - 1`; `generate_original_realization` identifies that cost with the original cut realization.

A possible induction uses the exact chooser: a unique-color detachment removes one current color, while either mixed-cherry detachment leaves the distinct current color count unchanged when no color is unique. The needed finite color-count identities and weighted list recurrence have not been formalized here. This paragraph is a proposed route, not a proved import.

## Implementation work

The existing `CoreProgram.run_prefix_work_bound` counts visited recursive prefixes and child attempts. A separate theorem must bound the actual tree/list/address work of normalization, chooser search, erasure, output assembly and copying by a polynomial in the original input size per charged prefix. The current package has exact payload permutations and retained-origin sublists, but no operation-cost semantics or polynomial bound.

## Complete algorithm

The parent must compose the accepted source core, a raw mass theorem and polynomial work with every ordinary rooted-MAF branch, the initial `q = k - 1` convention, all source/target interfaces and the final recurrence at a base strictly below 2.3391. No completed faster algorithm, runtime exponent or publication novelty claim is made by this package.
