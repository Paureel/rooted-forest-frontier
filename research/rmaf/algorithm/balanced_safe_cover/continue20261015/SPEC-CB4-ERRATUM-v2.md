# CB4 existential-state erratum, 2026-10-15

Preserve the original frozen SPEC-CB4-GUARDED.md, code and receipts. Its phrase
that each state retains a full original minimum path is too strong when read
as quantifying every reachable search state. Fresh independent review found
two exact actual quotient-star budget3 states: original prefixes65 (cuts0,6)
and257 (cuts0,8). The original optimum is3, but every agreement partition
refining either prefix costs at least4. The retained quantifier receipt gives
the literal original trees, source partitions, completions and costs.

The corrected invariant is conditional and existential: FROM A STATE KNOWN
TO EXTEND SOME ORIGINAL OPTIMUM, the operations preserve at least one
retained such continuation or emit a guard containing one. Starting at the
root gives at least one surviving optimum path. Other searched states and
other emitted guards may preserve no original optimum. The cover's required
global existential property is unchanged.

No code or alpha/theta target changes. The fresh review independently checks
all18 covers, all24 emitted certificates and108 actual retained substitutions.
It finds no counterexample to the corrected conditional coverage argument.
Universal source/formal interfaces and the paid frontier bound remain open.
