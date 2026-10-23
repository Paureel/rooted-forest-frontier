# Source reading and provenance

Read in this session: retained `research/rmaf/sources/baseline/split-or-decompose-v2.txt`, PDF pp.3–10,17–18,24–26. Only the definitions and original Whidden branching cover are used mathematically. Other source statements are context; their correctness is not imported as an axiom.

| Read claim | Exact retained locator | Verbatim source bytes |
|---|---|---|
| Original agreement requires vertex disjointness | PDF p.4, Agreement forests (2) | `T [Bi]and T [Bj]are vertex-` followed by `disjoint inT` |
| Rooted restrictions suppress unary internal vertices | PDF p.4, Rooted trees | `all nodes that have indegree-1 and outdegree-1` |
| No rho convention is required here | PDF p.4 footnote 2 | `We do not adopt` followed by `this convention here` |
| Ordinary cuts and component count differ by one | PDF p.5, Section3.1 | `at mostk−1edge cuts in T′` |
| Rooted pendant cuts use directed tails on the path | PDF p.6, Section3.2 (WHIDDEN) | `tails, but not heads, lie onP` |
| Rooted branching cover has the two singleton cases and all pendant edges cut | PDF p.6, Section3.2 (WHIDDEN) | `a is cut off,b is cut off,allthe e1,...,et edges are cut off.` |
| Hard2 literal components include the upward remainder | PDF p.18, paragraph before Lemma13 | `X1,X 2 and S∪{a,b}` |
| Figure16 consumes this hard2 branch after priority rules | PDF p.24, Figure16 step2e | `Whidden(t= 2)(2.42), followed by branching rule 6 or 7 if applicable.` |
| Improved runtime is a separate claim | PDF p.25, Lemma16 | `followed by branching rule 6 or 7 if applicable` |

Derived here, not retrieved: formal transport of an actual original target cherry through `restrict` and `RootedIso`; the pendant exclusion predicate; original block cut-side agreement; literal residual-component construction and no-leafless theorem. No source-only assertion that these claims are already formalized was assumed.

Frozen core/geometry/integration/original-graph sources were read as DEVELOPMENT imports, not independent certification. Exact import hashes are checked against `cut_realization/CUT-REALIZATION-MANIFEST-v1.json`. No unfinished assembly, whole_source_mass, pair_case, review proof, core_work proof, or root safe-cover proof was read.

Controls were pinned by construction before the first production theorem. They share Lean and the original checker with the production proof and cannot serve as independent universal certification. The parent protocol must assign a fresh hostile/nonauthor verifier; this arm does not spawn children.
