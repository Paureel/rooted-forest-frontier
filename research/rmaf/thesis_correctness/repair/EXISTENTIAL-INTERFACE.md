# Existential branch interfaces

The source's alternatives identify a branch containing some optimum. They do not state that every minimum original-edge cutset contains a listed branch's edges. The raw four-leaf control disproves the stronger interpretation. The earlier conditional proofs are preserved; their universal Cover premise will not be used as a forest fact.

For a fixed state F, define Opt_F(E) to mean that E is a minimum-cardinality original-edge cutset yielding an agreement forest with the compatible active F1. Write A(E), C(E), B(E) for membership of the selected endpoint edges and of both pendant edges. The A2BC input needed by the logical selection proof is:

    exists E, Opt_F(E) and (A(E) or B(E) or C(E)).

If no optimum satisfies A or B, this supplies an optimum in the C child. The exchange premise is used only on optima containing the child's C edge: if such an optimum also contains either protected pendant edge, an optimum satisfying B exists, contradicting failure of B. The protected-C form swaps A and C. The review's three axiom-free lemmas formalize this conditional logic; they do not establish forest coverage, exchange or transport.

BCY likewise needs only existence of an optimum in X, B or CY. If inherited exclusion rules out X, existence survives in B or CY. The earlier universal-per-cutset BCY premise is unnecessary.

Original-edge transport remains a separate graph requirement. For every optimal residual completion in a selected child, the lift must produce an optimal predecessor cutset containing the child's original cut edges. If a residual cut edge inherits protection, the lift must be choosable to include a protected original edge in its compressed path. Distinct compressed paths and earlier cuts must stay disjoint so this choice preserves cardinality. These requirements cannot be inferred from equality of yielded partitions alone.

The source writes coverage as an optimum-decrease equality after cutting and suppressing. Connecting that scalar statement to original-edge membership requires cutset projection/lifting. The logical consumers below keep this dependency explicit; no global marked-state invariant is assumed.
