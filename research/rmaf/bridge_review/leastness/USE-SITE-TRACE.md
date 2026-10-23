# Field and consumer trace

This trace covers every new constructor field and both uses of the original
region consumer. All paths are repository-relative. The kernel composition is
`lean/ActualEmbedding.lean`; no prose bridge is used to fill a structure field.

| Required field or use | Delivered statement | Hypotheses retained | Ruling |
|---|---|---|---|
| `GraphRegion.lean:146` ambient | `embedding_ambient_exact`, `embedding_ambient_iff` | Actual Tree input | Exact `vertices t` and inductive valid-address interpretation proved. |
| `GraphRegion.lean:147` terminals | `embedding_terminals_exact`, `embedding_terminals_iff` | Selection list; repeats allowed | Exact actual selected leaf occurrences; no uniqueness assumption. |
| `GraphRegion.lean:148` terminal nonempty | `terminal_nonempty` | An occurring label selected: hx and hs | Derived from occurrence/executable leaf correspondence. |
| `GraphRegion.lean:149` connected support | Earlier `extractedSupport` and nonempty extractor theorem | Same hx and hs | Same unchanged `minimalVertices` output, exact list equality. |
| `GraphRegion.lean:150` inAmbient | `minimal_in_vertices` | Output membership | Ambient validity derived; no caller geometry assumption. |
| `GraphRegion.lean:151` containsTerminals | `terminals_in_minimal` | Selected occurrence membership | Every occurrence survives root-prefix suppression. |
| `GraphRegion.lean:152` minimal | `minimal_least` | Competitor connected and contains all terminals | Proves required inclusion; stronger theorem needs no competitor ambient premise. |
| `GraphRegion.lean:159` region | `embedding_region_exact` | hx and hs | Membership equals exact original extractor. Root/convexity inherited from audited graph proof. |
| `GraphRegion.lean:165` deepest-root consumer | `embedding_consumer` | hx/hs for each input; root depth inequality; exact-output overlap | Calls original MinimalEmbedding consumer; result translated by exact list equality. |
| `PureBridge.lean:23` deepest root in neighbor | Original consumer ultimately applies RootedRegion theorem | RootedRegion below/convex structure; depth; overlap | Those fields now come from actual extractor connectivity. No degree-two or exchange claim follows. |
| Label uniqueness expected for `RMAF.Instance` | `instance_left_unique_occurrence`, `instance_right_unique_occurrence`, occurrence iff below n | Actual Instance permutation fields | Exactly one occurrence per valid label derived on each tree separately; no equality of their addresses asserted. |

`LeastEmbedding.minimal_least` itself uses `ConnectedSupport.toRootedRegion`
at its final proof lines: `below` makes the competitor root a common ancestor
of all selected terminals, and `convex` forces the given emitted vertex between
that root and its terminal descendant. Both hypotheses are explicit in the
proof. This use requires no leastness of the competitor and no assumed hull
identity. Therefore it is not circular through the MinimalEmbedding field that
is being constructed.

Remaining use sites outside this target include actual restriction/suppression
maps between source and target trees, degree-two cut transport, marks, global
refinement compatibility and the `ExchangeSystem.clearRest/freeLeft/freeRight`
fields. None is supplied here. This trace makes no ruling on unfinished
triple-family code or on the safe-cover/Whidden parameter audit.
