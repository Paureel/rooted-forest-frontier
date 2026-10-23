# Consuming interface

The public target is `assembly/HARD-PARENT-REFINEMENT-TARGET-v1.md`. No unfinished assembly proof file was read or imported.

| Public hypothesis or conclusion | Exact proof object |
|---|---|
| Proper original rooted binary trees | `RMAF.Tree` is binary syntax; distinct original source leaves are `(leaves S).Nodup` |
| Same original labels | Original `RMAF.agreement` contains both exact source/target partition checks; `agreement_cherry_source_labels` derives endpoint source membership |
| Actual target cherry, sibling swap admitted | `Safety.ActualCherry`, `actual_hard2_unordered_safety` |
| Unique original a–b path | `Components.pair_minimal_path` identifies executable minimal span with `VertexGeometry.PathAt` between original leaf addresses |
| Exactly two actual pendant directed child edges | `(pendantOriginal S a b).length = 2`; `original_pendant_spec` proves equivalence to original child-edge/path semantics |
| Literal original P=[A,B,C] after those cuts | `Executable.literalThree S q r`; `LiteralOriginalThree.leafsets` gives exact residual-walk characterization |
| Three nonempty components, no leafless regions | `LiteralOriginalThree` fields `covers`, `separated`, three `nonempty_*`, `no_leafless` |
| C contains a,b | `Safety.hard2_endpoints_in_root` |
| Every actual original agreement F | `actual_hard2_source_safety` or named-cut `actual_hard2_named_safety`; F appears only in the original `agreement` hypothesis |
| Singleton a OR singleton b OR F refines P | Conclusion of both safety theorems, using `VertexGeometry.Refines` in the required direction |

For fixed source S,a,b, first obtain q,r from the two-element `pendantOriginal` list. The same named q,r then work for every agreement F; the cuts do not depend on F. `actual_hard2_named_safety` accepts the list equality and produces the literal residual-component record together with refinement. The endpoint cases can be consumed separately through `actual_cherry_endpoint_alternative`.

The first mathematical call requested by the public hard-parent target is discharged by these theorem types. Actual assembly composition and fresh nonauthor verification are still pending outside this arm. No conclusion concerning the full algorithm or a branching factor below 2.3391 follows from this local source safety result alone.
