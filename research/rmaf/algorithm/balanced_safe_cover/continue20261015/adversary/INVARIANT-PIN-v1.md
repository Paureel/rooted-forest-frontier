# Reverse-caterpillar invariant, frozen after discovery pilot

This is a post-pilot mathematical conjecture pin, not held-out certification.
For C_N=(x1,(x2,...,(x(N-1),xN)...)) and its order reversal, every triple
is incompatible and there are no pair-path conflicts. Use pendant p_i and
gap g_i between xi and x(i+1), 1<=i<=N-2. For N>=5 the maximal columns are
exactly U_N={g_2,...,g_(N-2)} union {p_3,...,p_(N-2)}. Projected triple
{a<b<c} has its interior pendants and gaps with a<=i<c.

Conjectured exact invariants to test: each projected minimal row has size>=2;
for N>=6 its size-two rows are exactly {g2,p3} and {p_(N-2),g_(N-2)}.
For N=5 there is one additional row {g2,g3}. The selected minimum row under
preorder ids is {g2,p3}. Choosing g2 leaves the reverse-caterpillar family on
N-2 active labels after dynamic quotient. Choosing p3 leaves that family on
N-1 active labels. Equal columns from the suppressed gap have one original
representative; no original edge is reinterpreted as a cheaper cut.

Small exact check plan: N=3..13 formula rows against freshly built tree H;
for N=5..13 verify maximal columns and size-two classification; verify the two
selected left-row transitions symbolically after filtering minimal rows,
column quotient and relabeling. Exhaust all executed recursion nodes at the
failed budget b-1 for odd N=2b+1, b=2..6, expecting full binary depth b-1,
2^b-1 nodes, every internal rank2 and every leaf nonempty. Positive singleton
and empty controls plus corrupt max-column and size-two-row formulas must
fail. No new broad census. Stop any case exceeding 10 seconds.

If proved as a general invariant: at depth d<=b-2 active N>=2b+1-2d>=5,
so each node of failed SEARCH(b-1) has two children. Hence at least2^b-1
nodes on one initially connected incidence factor with n=2b+1 labels. This
would refute O*((3/2)^b) for literal SPEC-CB1, even with polynomial factors,
without counting multiple outputs. Reduced eligibility stays separate.
