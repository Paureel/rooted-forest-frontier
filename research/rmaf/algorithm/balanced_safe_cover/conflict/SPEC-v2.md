# GLOBAL-C v2 addendum: column domination

2026-10-15. Original `SPEC.md`, controls, all receipts, and failure logs remain frozen. This addendum licenses a universal constituent, not a new alpha/theta cover.

C4: for each original source edge e form its conflict incidence column I(e). Choose one canonical original edge from each inclusion-maximal nonempty column class. Mapping a transversal through incidence supersets preserves hitting and cannot increase set cardinality. Therefore at least one original optimum uses only these representatives. Kernel obligation: generic hit-preserving replacement and length preservation; source obligation: C1 and normalization; finite obligation: original-edge candidate restriction preserves exact optimum. No bound on the number of maximal classes is assumed.

Frozen abstract controls, by construction:

- H=[{0,1},{0}]. Incidence(1) is strictly contained in incidence(0); one representative 0; optimum 1.
- H=[{0,1},{1,2},{0,2}]. Three incomparable maximal columns; optimum 2; maximum disjoint hyperedge packing 1. No singleton hits every hyperedge.
- H=[{0,1,2,3}]. One equal-incidence class, representative 0; optimum 1.
- H=[] on four original edges. No representatives; optimum 0.
- Deliberate invalid domination: H=[{0},{1}], replace cut edge 0 by 1. Clean cutset {0,1} hits; corrupted {1} misses {0}. Reject the replacement.

The rooted-tree example incidence counts were inspected during construction and are exploratory confirmations, not untouched controls: incompatible triple M=1, equal-half failure pair M=1, crossed balanced quartet M=5. Their values cannot independently certify C4.

After controls, enumerate every n<=4 pair, restricting minimum cutsets to maximal column representatives and comparing the partition oracle optimum. This is a finite regression check. Do not rerun the already complete all-cutset n5 census without a new concern. No proposed algorithm is allowed the exact optimizer used in this check.
