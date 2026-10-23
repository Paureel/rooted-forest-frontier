# CB2 closure clarification, 2026-10-15

This addendum preserves SPEC-CB2.md and all original receipts. It clarifies
the already implemented stopping rule; no code or mathematical target changes.

At each closure iteration, apply one maximal-column projection and row
subsumption. If the resulting minimum row is singleton, select its original
edge, remove hit rows, and repeat. Stop immediately when the projected
minimum row is nonsingleton, or when no row remains. The operation does not
continue a nonsingleton projection to a fixed point.

Fresh review froze the stronger fixed-point interpretation before reading
the parent code. It differs in 16 of the 26 stored profiles, all in row29's
edge2 residual state. Prefix masks, prefix costs, retained branches and exact
masses agree in all26 row compilations. The review retains both computations
and labels the literal stop-mode replay as post-implementation contact.
The stronger rule is not adopted by this clarification. Future adoption would
require a new version and fresh source-bound receipts.
