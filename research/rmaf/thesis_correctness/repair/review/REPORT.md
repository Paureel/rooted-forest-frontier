# Fresh normalization review

The component proof supports root-safe **full-path** normalization under its explicit surviving-fragment hypothesis, including compound endpoints. The strict repair of an empty proper common subtree supports survival for a globally minimum current-forest cutset. These are reviewed prose arguments. The independently rebuilt Lean files establish the stated local list, graph-walk, binary-cut, arithmetic, and conditional-logic lemmas. They do not formalize agreement-forest preservation.

The overall repair remains open. The missing general statement must lift an optimal residual completion to an optimal original-current-edge cutset, preserve the selected branch edges and count, and allow a designated protected origin on a compressed path to be selected. It is used in existential branch coverage, the source's construction of E0 after sequential branches, and the persistence of protection along the promising path.

## Construction grades

| Construction | Grade | Exact scope |
|---|---|---|
| Component route | Reviewed | N_anchor full-path normalization and strict empty-common-subtree AF repair, for the finite reduced binary current-forest model and explicit compatibility hypotheses in PROOF-TARGET.md. |
| Component consumer chain | Conditional | Minimum fragments and their propagation to compound u are justified. The source's raw-edge optimal-completion inputs and general lift remain assumptions. |
| Original-edge route | Reviewed | The 26 named OriginalEdges/RootedPaths theorems about list membership, counts, provenance, walks and ranked parent maps. |
| Original-edge full AF construction | Conditional | Rooted labelled restriction isomorphism and F1 embedding disjointness are supplied by the component prose argument, not by these Lean files. General suppression/protected-origin transport is absent. |
| Scalar and existential consumers | Reviewed | The frozen natural-number inequality and the stated implications with coverage, exchange, inherited exclusion and lifting as explicit inputs. |

The exact normalization theorem and its proof reconstruction are in [LOCAL-RECONSTRUCTION.md](LOCAL-RECONSTRUCTION.md). In that theorem, A and C must be identical complete proper endpoint subtrees before E is cut; an E2⊆E preserves those complete subtrees and makes them siblings. The AF premise concerns the actual compatible current forests. For one path cut, a detached labelled fragment that reconnects to outside labels requires an endpoint label already connected to the LCA. Both endpoint fragments surviving is a sufficient simpler hypothesis. With at least two path cuts, full restoration inserts the actual LCA-parent edge only if it exists. The exact count is |E|−|D|+δ, with δ the indicator of a genuinely new parent cut.

## Source and interfaces

The source read covers printed pp.12–18, 101–103 and 112–116 of the retained Whidden thesis; printed pp.102,113,116 were also rendered and visually checked. Page12 fixes the unary labelled rho and suppression conventions. Page16 permits compound sibling roots. Page17 Lemma2.2 gives the containment bridge between active and original forests. Page18 gives the forest compatibility conditions. Exact local extracts and page locators are retained in [source-ledger.json](source-ledger.json).

| Use site | Ruling |
|---|---|
| Lemma6.5, p102, one-cut anchor | Refuted for arbitrary compound E without a survivor. The executed witness has containment and AF compatibility, three cuts and optimum one. |
| Lemma6.10, pp112–113, first exchange | Global minimum E0 supplies A,C,X survivors. Adding the two pendant cuts preserves them. Full normalization is justified; the source's selected E3 is not automatically every E0 path cut. |
| Lemma6.10, p113, second (x,u) exchange | The first full restoration joins the two surviving endpoint fragments at u and leaves x's survivor unchanged. Intermediate optimality is unnecessary. A corridor-specific representation argument is reconstructed below. |
| Lemma6.10, p113, counting | Use actual cuts and inequalities. The equality E′1=E1 does not follow from E⊆E0. No executed in-regime counterexample to that equality is claimed here; its use is classified as an unsupported import. |
| Theorem6.12, p116, ordinary A2BC | Full normalization gives the required existential optimum containing both pendant cuts. It need not equal the source formula restoring ec alone. |
| Protected-c A2BC | Swapping endpoints gives the same fixed-forest exchange. The existing protected_c_existential_branch theorem uses precisely this swapped exchange hypothesis. |
| BCY and inherited exclusion | The conditional Lean deductions are valid. Forest coverage, old-protection exclusion and protected-origin lifting remain inputs. |

The reviewer supplement proves a narrow representation statement for Lemma6.10. After cutting exactly the two pendant edges P, only internal vertices on the a–u and c–u arms are suppressed. First full normalization removes every cut on these arms. Consequently C1\P consists of unchanged current edges of G=F2~P, has size |C1|−2, and preserves the u and x fragments. The second path is exactly {ex,eu}, and the incoming edge of their common parent is unchanged or absent. Adjoining P transports the second result back to the same original current edge set. This supplement needs a further independent read before the entire two-exchange chain receives a multi-pass completion grade. It does not prove the general lift required for arbitrary protected states.

## Executed checks

The reviewer wrote `fresh_exact.py` before reading either construction proof. It uses original vertices, minimal labelled hulls, canonical rooted restrictions and disjoint embeddings, importing only Python's standard library. The five frozen forest fixtures and five frozen scalar controls all reproduced. The deliberately wrong AF, optimum, partition, scalar and parent-existence outputs were all rejected. The first run stopped only because equivalent partition blocks were serialized in a different order; the recorded correction made that comparison order-insensitive.

| Exact check | Executed result |
|---|---|
| Raw Cover fixture | Optimum 2; a minimum original cutset lies outside A/BB/C; a covered optimum also exists. |
| Bad normalization and compatible twin | Original AF true in both; normalized AF and active containment are false in the bad fixture and true in the twin. |
| Missing root parent | Parent absent; normalized forest remains an AF. |
| Compound empty fragment | Original AF true, normalized AF false; cut count 3, optimum 1. |
| Frozen scalar tuples | Final counts 2,3,2 for positive controls and 2,3 for the two negative controls. |
| Atomic partial-restoration fixture | Original AF true; partial restoration false; full normalization true; cut count 2, optimum 1. |

The complete four-leaf family included all 225 ordered binary tree pairs and the specified compatible whole/rho-detached states. It examined 51,516 AF cutsets, with 44,862 N_anchor premises, 42,204 two-survivor premises, 7,152 compound two-survivor premises, and 4,710 absent-parent two-survivor premises with at least two path cuts. It also checked 5,070 empty-subtree repairs and 9,897 minimum-survival instances. No failure occurred. The family does not include every possible yielded active forest, and its counts are not a universal proof.

The additional consumer check passed 144 ordinary or swapped minimum exchanges and 136 two-stage minimum cases. The latter included 68 intact compound expansions and 92 cases lacking the second incoming parent. Four direct frozen-fixture cases also passed; deleting either required final pendant cut failed AF in each case, giving eight negative instances. The relevant receipts describe the finite families exactly.

All eight positive Lean files rebuilt from unchanged sources. Both intentional false controls were rejected: the phantom parent at a root, and the false lower bound of three cuts for an empty binary root. Every printed axiom dependency was empty or a subset of `propext`, `Quot.sound`, and `Classical.choice`; the delivered sources contain no `sorry`, `admit`, custom `axiom`, or `native_decide`. Rebuild logs and source hashes are retained in `lean-build/` and the Lean receipt. A successful compilation is reported only for each actual Lean statement.

## Failures and remaining work

[bugs.json](bugs.json) gives three machine-readable, executed reproductions: universal raw Cover, arbitrary compound normalization without an anchor, and unconditional substitution of partial restoration for full normalization. Each records its exact regime, expected and actual values, script and receipt. The last two witnesses are nonminimum and do not refute the minimum-cutset consumers. The standalone incompatible F1 fixture fails active containment and is explicitly excluded as a counterexample to the active-state theorem. No new counterexample to N_anchor or the strict empty-subtree repair was found.

The smallest general obligation is the protected-origin lift stated above. The corresponding exact statements and use sites are listed under `unproved_imports` in [verdict.json](verdict.json). A complete global conclusion would additionally require the marked-state induction and the algorithm's other branch lemmas. Global correctness, running time, root-convention transfer, and novelty have not been reviewed here.

The evidence is local. No app source, data, snapshots or plots were uploaded. No author proof, frozen result or aggregate theorem count was modified. The toolkit-wide `bootloops-check` suite was not run; the checks here are the retained fresh exact programs and the local Lean rebuilds. No new bibliography entry was added, and no external bibliographic verification is claimed.
