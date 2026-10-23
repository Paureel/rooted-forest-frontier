# Pinned retained/raw family interface

The X0 run returned NO-FIRE on its finite controls. It identified an important
distinction in the pin: charged closed regions contain labels, while a raw
uncharged open support may be leafless. Existing DP states require a retained
open region to have a nonempty local label set. Therefore the continuation
will not assume every raw open support is retained.

Use a finite labelled binary tree with distinct leaf labels and binary
addresses. A raw family has k indexed closed supports and at most one open
support. Closed supports are pairwise disjoint, path convex, nonempty in leaf
labels, and avoid the root. An open support is path convex, contains the root,
and is disjoint from every closed support; it may temporarily have no labels.
The supports lie in the tree and cover all leaf vertices exactly once.

Normalize closed supports to the least path-convex hull of their leaf
vertices. If the open support has labels, replace it by the least path-convex
hull of those labels together with the root. If it has no labels, discard it.
The cost is k, the number of closed supports. The number of labelled blocks
is k plus one exactly when the open support has labels. Thus discarding an
empty open support preserves cost and labelled block count; it does not
preserve the number of raw support objects, and that number is not the target.

First universal target: this normalization produces a valid retained family,
preserves each closed block's leaf vertices and the open block's leaf
vertices, preserves disjointness/coverage and closed cost, and proves the
claimed least-hull normal form. Hull is defined by intersection of all
path-convex supersets; its convexity and least property must be proved. A
separate graph/path-union or executable-RMAF correspondence is not assumed.

The original frozen controls use `family_valid` for retained families, hence
reject their `charged-leafless` row, whose open support is actually uncharged
and leafless. That row is not an in-regime refutation of raw-family pruning.
The new amendment freezes the raw interpretation and its exact cost before
the author constructs the formal model. No old control or receipt is changed.

Full four-transition family restriction/assembly, color/mask state decoding,
and executable extraction remain separate obligations after normalization.
