# Family adversary report

The X0 search returned **NO-FIRE**: no admitted family failed the exact checks on the five fixed trees. Here NO-FIRE means only that this bounded search found no counterexample. The family theorem, source-suppression correspondence, and graph-to-DP correspondence remain open at this stage.

I wrote the work skeleton after reading `FAMILY-TARGET.md`, then read the existing specification in `PROOF.md` and the accepted `ConnectedRegions.lean`. I did not open a new author family model, implementation, or proof. I wrote `controls-v1.json` and its SHA256 before constructing `check_family.py`; the full run checked that SHA256 before loading the fixtures.

## Exact checks

`results/triple-family-adversary-v1.json` contains 11 passing positive fixtures and six rejected corruptions with passing clean twins. The fixed-tree search considered 677 nonempty vertex supports and admitted 119 family records formed from one such support plus singleton regions for every uncovered leaf. Different choices can give the same family with a different region ordering. This generation tests extensions and incursions but does not enumerate all disjoint families. The admitted counts were 1 on the singleton, 5 on the cherry, 14 on the three-leaf tree, 31 on the balanced four-leaf tree, and 68 on the specified five-leaf tree.

For every admitted family, the checker tested that each trimmed support stays inside its original support, preserves its exact label block, remains path-convex, and stays disjoint from the other supports. It checked the number of blocks and the closed-region count. It restricted the normalized family to each child, assembled the child families back with their original block identities, trimmed after closure, and compared the result with the parent's normalized family. The exact cost equation was the sum of the child closed counts plus one for each child open block closed by that transition. The run included 37 unused-root cases, 26 left extensions, 18 right extensions, 37 joins, and one leaf case.

The checker uses explicit graph adjacency and breadth-first paths. Its expected fixture sets were written by hand. Those sets and this code share an author, binary-address conventions, the specification, and the Python runtime; the controls are construction evidence for this checker. They cannot later count as withheld certification of an author proof or implementation that uses them. The original regression examples also remain regression evidence.

## Exact witnesses

Addresses below are binary strings, with `ε` denoting the empty root address. Full machine-readable supports, labels, expected results, and caught error codes are in the controls and receipt.

| Control | Exact observation |
|---|---|
| Gapped LCA closure | `{ε,00}` is LCA-closed but misses `0` on the path. Adding `0` gives the passing twin. |
| Leafless incursion | On leaves `00=a,01=b,10=c,11=d`, open supports `{ε,0,00}` and `{ε,0,00,1}`, with the other leaves as singleton regions, both trim to `{ε,0,00}` and the same three singleton regions. Both have four blocks and closed count three. |
| Empty child charge | The second incursion support restricts to `{ε}` in the right child with no labels. Discarding it leaves two closed singleton blocks and count two. The planted count three is rejected. |
| Root singleton | A singleton tree has support `{ε}`, one open labelled block, and closed count zero. |
| Unused internal root | The cherry family `{0}`, `{1}` leaves `ε` unused and has two closed blocks. |
| Closed stem | On `00=a,010=b,011=c,10=d,11=e`, closed support `{0,01,010,011}` trims to `{01,010,011}`. The other three leaves remain singleton regions. |
| Open stem | On the same tree, open `{ε,0,00}` must retain its stem. Replacing it by `{00}` is rejected because the open support no longer contains the root. |
| Intermediate vertex | The closed `a,b` span `{0,00,01,010}` must retain `01`. The planted LCA-only support `{0,00,010}` is rejected for failing path convexity. |
| Adjacent bad color | For target `((a,b),c)` and source `((a,c),b)`, open `{ε,0,00,01}` and singleton `{1}` stay separate. Their source spans are disjoint before and after trimming. Merging them is rejected as the forbidden full bad triple. |

The search discarded 21 raw leafless child fragments. Every normalized family in the admitted set had no occupied child fragment without a label. The exact leafless pair demonstrates that distinct raw supports may normalize to the same family; preserving block identities and costs suffices for these checks.

## Required hypotheses

The combined target and existing specification support the following interface. A finite full binary tree has distinct labels on exactly its leaves. Retained region supports are nonempty, pairwise vertex-disjoint and path-convex, and cover each labelled leaf exactly once. At most one region is open; it is exactly the region containing the current subtree root. Every retained region, including the open region, has a nonempty local label set. Region identifiers stay separate even when colors agree.

The short target's requirement that each **charged** region contain a label does not by itself exclude a leafless uncharged open region. The existing specification supplies the stronger convention: `PROOF.md:29` says, “We may thus require every open region to have a nonempty label set below its boundary.” A cherry with open support `{ε}` and closed singleton supports `{0}`, `{1}` satisfies the charged-region clause alone. Its open label block is empty. If such a raw object is allowed, discard the open fragment before applying the normalized-family statement; the two labelled blocks and their cost survive, while the raw support-list length changes. The post-run illustration is retained in `results/triple-family-adversary-boundary-v1.json` and is not additional preregistered evidence.

Root membership also needs an explicit hypothesis. In the frozen wrong-open control, supports `{00}`, `{ε,0,01}`, `{1}` form a valid family when the second support is open. Designating the first support open would extend it outside its original support by adding `ε` and `0`. The checker rejects that designation before trimming. This is a hypothesis-omission control; it does not refute the convention in `PROOF.md:29`.

For child restriction, discard each nonempty support fragment whose local label set is empty before assigning child states or closed counts. A discarded fragment contributes no block, state, or charge. For assembly, retain block identifiers through extensions and join only the chosen continuing child blocks. Closing an active block adds one and permits trimming its now-closed support to its labelled span. These statements describe the interface attacked here; their universal proofs remain the author's obligation.

Preserving each block's labels also preserves the inputs to every source-tree span computation. The executed cross-tree check covers the stated bad-triple regression only. The checker does not prove that target disjointness implies source disjointness under suppression, and it supplies no general G1 theorem.

## Replay and limits

From the workspace root, run:

```sh
./bootloops-python research/rmaf/triple_dp/family/adversary/check_family.py --controls-only --output /private/tmp/triple-family-adversary-controls-replay.json
./bootloops-python research/rmaf/triple_dp/family/adversary/check_family.py --output /private/tmp/triple-family-adversary-replay.json
```

The retained pilot ran in 0.0012202920006529894 seconds and the bounded run in 0.015003124999566353 seconds, measured inside Python on this configuration. These are scheduling observations. The scientific checks are the exact set and integer comparisons above.

No Lean theorem, compiler diagnostic, axiom audit, independent fresh-author replay, full toolkit validation suite, or author-code review was run by this arm. The negative diagnostics here come from executed Python comparisons against specified false transformations. Formal acceptance still requires the target's fresh semantic, axiom, and false-proposition controls. This report does not alter an earlier receipt or increase an earlier theorem/census count.
