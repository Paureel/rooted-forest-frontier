# Lifting use sites

These are source extractions and open interface requirements, recorded before construction. They do not assume that the target lemmas hold. Source: retained Whidden July 2013 thesis, printed pages below; PDF page equals printed page plus 13.

| Source site | Actual source quantity or rule | Required lifting statement |
|---|---|---|
| p.15, definition of e | Minimum number of actual current-forest edges whose deletion and yield is an AF of the fixed target trees. | Acceptance depends on the yielded labelled forest; prove L1-L3 before identifying a forced-extension minimum with a residual optimum. |
| p.107, inherited protection | A suppressed vertex replaces its remaining two incidences by one edge; that edge is protected if either original incidence was protected. | Derive the path of actual original edges, show which origins survive, and select a designated protected origin when lifting a cut residual edge. A Boolean flag alone proves none of these. |
| pp.112-113, Lemma 6.10 | Sequential optimum decreases are used to choose E0 containing a selected prefix. | Convert each stated equality into existence of a minimum raw cutset through L4, composing actual residual path origins. The reviewed local two-exchange proof assumes that E0 explicitly. |
| p.114, Theorem 6.12 definition | An invocation is promising when `|F2| + e(T1,T2,F2) = 1 + e(T1,T2,T2)` and `k0-k = |F2|-1`. | Relate cumulative raw cut cost to the component increase. Empty discarded fragments can invalidate this equality for arbitrary cuts. This normalization requires a separate lemma. |
| p.115, later forbidden branch | For two promising consecutive invocations the source infers an optimum drop by the branch cut count. A protected sibling of an edge incident to an unlabelled root is treated as an alternative cut yielding the same forest. | Prove the numerical inference from explicit identities; prove actual root-sibling yield equivalence and its relationship to the designated original protected origin. Do not assume a generic residual optimum is globally optimal. |
| pp.115-116, earlier protection event | A later residual optimum cutting the descendant protected edge is used to make an earlier left branch promising. | Sequential L2/L4 lifts with compatible AF target, additive cost, and selection of the inherited origin. Account separately for common-subtree contractions that change labels. |
| p.116, final A2BC exchange | The source chooses an original minimum E0 containing ec and a pendant cut, then obtains a minimum containing both pendant cuts. | The completed repair reviews the fixed-current-forest exchange. The new investigation must supply the raw minimum-existence and protection transports used before and after it. |

The source's component-based promising definition is stronger than an informal statement that a child looks useful. Its two equations must be proved for the chosen path. The arbitrary-child rejection control has equal trees, an unnecessary cut C and residual optimum zero: residual optimality cannot imply global optimality there.

## Cost normalization to audit

Candidate CN: for a reduced labelled forest F with no empty input component and a raw cutset C, the number of components of yield(F-C) is the number of components of F plus |C| minus the number of label-free components of F-C. A possible further consequence is that if C is contained in a globally minimum AF cutset, no label-free component occurs and every cut contributes one labelled component. These are new open claims, not imported assumptions. Before a construction uses them, a separate exact control/search must check the empty-component correction and the minimum-prefix consequence.

The frozen empty-component control has one input component, four raw cuts, one discarded empty component and four yielded labelled components. It rejects replacing raw cost by component increase without a hypothesis. The constant `1` in the source promising definition also depends on starting from a single augmented tree; arbitrary current input forests require their own initial component count.

## Contractions

L1-L3 cover actual edge deletion and yielding on a fixed labelled graph. Contracting an identical full common subtree to a new label changes that graph and its label set. Expansion must preserve the acceptance predicate in both current forests, and a cutset projection must account for internal cuts. S_every and S_exists are under a separate X0 audit. Neither is currently available as an assumption.

No runtime or convention-transfer result is imported into this map.
