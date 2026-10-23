# Literal predicate inspection model

`literalMeter` refines the exact Boolean value of the frozen `LiteralProps` instance. Its bill uses the existing source primitive model: one scalar Nat/Bool comparison is one inspection, while recursive scans and data construction are explicit. `checksMeter` keeps the 17 conjunction tests in source order and stops on refusal. Its list of thunks does not precompute the later tests. `literal_value` proves the decision equality for every input; `literal_work` proves a polynomial bound for every bounded payload, including refusals.

| Frozen guard | Charged implementation |
|---|---|
| `properPair T S=true` | Existing `properPairMeter`, including repeated leaf extraction |
| `subtree S R.w=some (bottom ...)` | Existing subtree meter, recursive exact tree equality, ten constructor/orientation inspections |
| Bounded cherry existential | Existing vertices meter, left-to-right bounded existential, both endpoint orders with separate subtree tests |
| Two source cuts | Existing cuts meter, full length traversal and scalar test |
| Bounded core-label equivalence | Full target leaf extraction; at every visited taxon, separate C/X leaf extraction and membership scans, Iff/scalar tests |
| `R.b` in core leaves | Existing core leaf extraction and early-stop membership |
| `d.c` outside core leaves | Separate core leaf extraction/membership, negation |
| Three `LeafAt` tests | Separate existing subtree/leaf equality meters |
| Incident equality in either order | Each visited disjunct separately extracts X leaves, executes the existing incident meter, and compares the address list; second disjunct skipped after success |
| Two tail memberships | Separate dropLast traversals, X leaf extraction, existing minimal-vertex generation and address membership |
| Two off memberships | Separate X leaf extraction, minimal-vertex generation, address membership and negation |
| Source boundary labels | Existing subtree-label meter, separate X leaf extraction, ordered Nat-list equality |
| Endpoint order | Four scalar comparisons and logical decisions, conservatively charged nine inspections |

The bounded existential and universal follow the computable `List.decidableBEx` and `List.decidableBAll` source instances. The logical conjunction and disjunction instances use macro-inline Bool operations; the Iff instance compares both computed Boolean values. The original `Decidable` body and these standard implementations are identified in `READING-LEDGER-v1.json`. Tree/list equalities may compare symmetric operands; `tree_eq_value` and the list equality value theorems prove their exact values, and their recursive bills include all inspected constructors and labels.

`literal_call_work` requires the exact frozen call domain and the enclosing selected-address bounds. `paid_selected_work_concrete` derives those bounds and installs `literalFee` in the frozen paid selected meter. `literal_budget_expanded` proves the polynomial coefficients; no fee constant is supplied by the caller. `literal_call_scalar_bits` preserves the label-width information for a later binary cost interpretation. Native trace semantics, binary operations, and instrumentation overhead are outside this inspection model.
