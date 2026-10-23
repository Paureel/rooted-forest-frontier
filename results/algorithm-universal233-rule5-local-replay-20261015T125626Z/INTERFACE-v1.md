# OPEN author interface

Namespace `Universal233.Rule5Local`; actual rooted trees and original labels
are `RMAF.Tree`, with no implicit root label. Read FIRST-GAP-v1.md before use.

| Declaration | Exact delivered use |
|---|---|
| `admitted` | Finite actual source guard: proper equal labels, actual cherry, all cherries t2 in both orientations, both syntactic Rule4 exclusions, exactly two good literal parent restrictions and both parent embedding checks |
| `incident` / `incident_spec` | Literal original arcs crossing the actual minimal X hull, root incoming edge excluded |
| `actual_one_incident_split` | Proper T, incident(T,X)=[q] implies original X labels equal the descendant or root side of q |
| `commonSplit_emits` | Adds membership of a literal original source pendant with X labels, and emits actual source/target split arcs; no marked solver theorem |
| `original_crossing_clusters_exclude_block` | Proper original T/S, incompatible actual original subtree clusters and one original AF block containing three witnesses imply contradiction |
| `figure153_forbidden_triple` / `figure153_block_exclusion` | Actual source caterpillar template, target root c and proper distinct labels prohibit b,c,X in one original block |
| `splitTwo_original` / `splitTwo_refines` | Two successive literal original-source splits preserve original agreement, add at most two blocks and refine the literal hard2 parent partition |
| `actual_hard2_exchange_from_split_saving` / `_b` | Constructs a no-larger original AF once the explicit computed split-length saving and endpoint singleton hold; the saving is not asserted globally |
| `case321_split_saving` / `actual_case321_exchange` | Derives saving and no-larger hard2-or-singleton-a cover from literal displayed source a/X/c geometry and actual target X+c descendant subtree |
| `case323_split_saving` / `actual_case323_exchange` | Derives saving and no-larger hard2-or-singleton-b cover from literal displayed source a/X/c geometry and target root c |

For Case321 and Case323, source lookup, actual original cut addresses and
target geometry are hypotheses. They have not been derived from `admitted`.
There is no accepted exhaustive selector-to-proof binding. In particular this
interface does not supply any theorem for large/two-leaf good pendants,
outside-second-cherry cover, Figure15.2 cover or every sibling orientation.

The Python selector/materializer returns literal original cuts, their actual
nonredundant cost, permanent original-label partition and role. Its finite
tests do not discharge the missing uniform graph implications. Child solvers,
budget/minimum assembly, role-swap/output reconstruction for the complete local
selector remain unfulfilled consumers. No full algorithm can use this package
as a completed Rule5 theorem.
