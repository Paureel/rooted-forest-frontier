# Nonauthor review of the completed CB1 lower family

The child author's reverse-caterpillar argument was read in full after its
completion. This review authored neither that family nor its independent
instrument. The parent CB1 implementation was already fixed before the child
reported the family. No child code was reused for the replay below.

The source proof's sections1 and2 use actual rooted triples and unsuppressed
pair paths. Opposite caterpillar orders disagree on every triple. Therefore
an agreement block has at most two labels. Consecutive pairs give disjoint
source and target intervals and attain the displayed cut count. This proves
the claimed optimum independently of a packing bound.

Sections3 and4 specify the retained original edges and quotient rows. The
end-gap domination requires at least five active labels; that hypothesis is
stated. Interior pendant/gap incomparability uses triples on the side with
at least three leaves. The L/R/G/A row classification is exhaustive by
endpoint/interior membership. The displayed antichain and repeated-column
claims hold under the stated index ranges. Filtering a subsumed row family
on a selected edge commutes with subsumption: if a containing row avoids
that edge, its contained witness also avoids it. The two active-size
transitions therefore match the actual retained-variable search, without
creating a suppressed replacement edge.

Section5 only needs two children and active-size loss at most2 through the
failed budget b-1. At depth at most b-2 the active size is at least5, so the
rank-two invariant applies. At depth b-1 a nonempty conflict remains at
budget0. Thus the complete binary tree node count2^b-1 follows. Initial
incidence factorization cannot remove it, because the family is connected.
The proof concerns failed-budget work of one-witness search, not the number
of output optima. This is the consuming runtime obstruction required by CB1.

Executed receipt algorithm-balanced-cover-continue-reverse-nonauthor-replay.json
uses the earlier parent solver on b=1,...,6, without importing the child's
code. Failed-trial node counts are1,3,7,15,31,63; all-trial counts are
3,7,15,31,63,127. Six off-by-one node comparisons were rejected. Each case
checks all rooted triples and a direct original-edge paired-interval
agreement certificate. The deepest shared layer is the mathematical tree
and conflict definition; the implementations and family constructors differ.

No source-model flaw was found in this review. The infinite quotient
invariant remains a handwritten argument; the finite replay and this review
do not constitute a source-bound Lean formalization. The correct grading is
reviewed prose plus independent finite implementation agreement. A full
VERIFIED-CLOSED label is not assigned. The exact3/2 bound is rejected for
literal CB1 conditional on this reviewed invariant. CB2/CB3 require their
own analysis, and safe-cover existence remains open.
