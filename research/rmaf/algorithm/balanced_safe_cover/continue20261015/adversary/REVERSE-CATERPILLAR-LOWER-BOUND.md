# A connected ordinary lower family for literal GLOBAL-CB1

Status: handwritten source-level asymptotic argument, with exact finite
implementation checks. It is not a Lean-checked theorem or a completed fresh
nonauthor review. The argument refutes the licensed O*((3/2)^b) generation
bound for the literal factorized, dynamically column-reduced, one-witness
SPEC-CB1 algorithm. It does not refute safe-cover existence or the restricted
alpha=2 proposal. No semantic failure was found.

The family was selected after the frozen controls and small pilots. The later
invariant checks are development evidence, not held-out certification. All
code was written independently of the parent's new solver and imports only
Python's standard library. No universal233, joint_macro, paid_cover, or parent
new solver implementation was read.

## 1. Actual original trees and optimum

For N>=3 put

    S_N = (x1,(x2,...,(x(N-1),xN)...)),
    T_N = (xN,(x(N-1),...,(x2,x1)...)).

These are ordinary rooted binary trees with distinct original labels and no
rho. Number leaves by their position in S_N. Write p_i for the original
pendant edge at xi, and g_i, 1<=i<=N-2, for the spine edge separating
{x1,...,xi} from {x(i+1),...,xN}. These names always denote original edges.
With the independent instrument's preorder edge numbering, g_i has id2i-1;
p_i has id2i-2 for i<N and p_N has id2N-3.

Every triple a<b<c has source rooted topology xb xc | xa, whereas its target
topology is xa xb | xc. Thus every triple disagrees. An agreement block has
at most two labels, giving at least ceil(N/2) blocks and at least
ceil(N/2)-1 original nonredundant cuts. Consecutive pairs in source order,
plus a singleton when N is odd, attain that bound. Their pair paths occupy
disjoint intervals of the spine in both trees; reversal changes interval
order and preserves disjointness.

For the lower-bound family choose N=2b+1, b>=2. Its optimum is exactly b.
An explicit b-cut source witness is

    {g_2,g_4,...,g_(2b-2),p_(2b+1)}.

It yields blocks {x1,x2},...,{x(2b-1),x(2b)}, {x(2b+1)}. Every source
component has labels, every block restriction agrees, and target supports
are disjoint in the original unsuppressed target.

## 2. Original conflict family and factorization

The conflict definition is exactly PROOF.md Definitions and C1, as invoked
by SPEC-CB1. Every triple contributes its original source span. No pair-path
conflict occurs: for four distinct caterpillar leaves, two pair paths are
vertex-disjoint precisely when their label intervals are disjoint; reversal
preserves that property. The source span of {a<b<c} contains its three
pendants and every spine gap g_i with a<=i<c, i<=N-2.

No original triple row properly contains another: its pendant edges identify
exactly its three leaves. The incidence graph has one connected factor.
Two triple rows sharing a leaf share its pendant edge. If two triples are
disjoint, a triple containing a leaf from each joins their incidence
components. Hence initial factorization cannot split the family. The
quotient families below also stay connected: their all-gap row meets every
other row through a gap.

## 3. Exact maximal-column quotient

For N>=5, precisely the following columns are inclusion maximal:

    U_N = {g_2,...,g_(N-2)} union {p_3,...,p_(N-2)}.

The first two pendant columns and g_1 are dominated by g_2: every triple
containing either first leaf must cross the first-two-leaf split. The last
two pendant columns are dominated by g_(N-2). There are no other edges.
Distinct retained gaps are incomparable. For j<k, a triple entirely within
{x1,...,xk} can cross g_j without crossing g_k, and a triple entirely within
{x(j+1),...,xN} can cross g_k without crossing g_j. Each side has enough
leaves because 2<=j<k<=N-2. A retained p_i is not dominated by a gap: the
side of that gap containing xi has at least three leaves, so a triple on
that side containing xi avoids the gap. No pendant dominates a gap, since
a crossing triple can avoid that pendant. Distinct pendants are
incomparable. Thus the stated universe is exact.

Project all triple rows onto U_N and remove proper supersets. Write I for
{3,...,N-2}. The resulting minimal row family K_N is exactly

    L_i = {p_i,g_2,...,g_(i-1)}                    (i in I),
    R_i = {p_i,g_i,...,g_(N-2)}                    (i in I),
    G   = {g_2,...,g_(N-2)},
    A_(i,j,k) = {p_i,p_j,p_k,g_i,...,g_(k-1)}      (i<j<k in I).

To derive this list, classify a triple by its labels among the first two,
the last two, and I. Two first labels plus xi give L_i; two last labels plus
xi give R_i. A triple using both endpoint pairs and no internal label gives
G. Three internal labels give A. One endpoint label plus two internal labels
has a row containing an L or R row. One label from each endpoint pair plus
an internal label contains G. These exhaust the triples. The displayed rows
are an antichain: L and R each have one distinct pendant, G has none, and A
has three; A rows omit both end gaps, so cannot contain L, R, or G. Their
pendant triples distinguish different A rows. L_i and R_i have disjoint
nonempty gap intervals, so neither contains the other.

No further column domination arises on K_N. The row G distinguishes each
gap from every pendant. L_i and R_i distinguish p_i from every gap: each
gap belongs to exactly one of them. L_i distinguishes p_i from any p_j.
For j<k, L_(j+1) contains g_j but not g_k, and R_k contains g_k but not g_j.
Both rows exist for 2<=j<k<=N-2. Therefore quotienting K_N again changes
nothing, apart from canonical representatives of equal original columns
created by prior cuts.

For N>=6 the only two-edge rows are

    {g_2,p_3},  {p_(N-2),g_(N-2)}.

For N=5 the third two-edge row is G={g_2,g_3}. Every other displayed row has
at least three edges. Thus the minimum row rank is exactly two whenever
N>=5. For N=3 or4 the quotient is one singleton row; N<=2 has no conflict.

## 4. Closure under the actual recursive branches

Under preorder ids, the chosen minimum row is {g_2,p_3}. Its gap has id3
and its pendant id4, so the first successful search follows the gap branch.
The asymptotic lower bound below does not require that order: for N>=6 any
minimum row is one of the two endpoint rows, with the same closure by
reflection. The extra N=5 row also has the stated size reductions.

Selecting g_2 deletes every crossing triple row. The first component contains
only x1,x2, so it contributes no remaining triple. The residual rows are
exactly those of the reverse-caterpillar pair on x3,...,xN, represented by
original surviving edges and then quotiented. Its active size is N-2.
Projected rows removed earlier by subsumption cannot reappear: a row
containing g_2 cannot be a subset of a row avoiding g_2. In the residual
family the old p_3,p_4,g_3 are dominated by the old g_4, giving the new
first-two-leaf boundary. All maximal columns of the smaller family are
present among the old retained columns. Thus the result is K_(N-2), up to
canonical original-edge representatives; the N=3,4 singleton cases agree.

Selecting p_3 deletes exactly the triple rows containing x3. Among the
remaining rows, g_2 and g_3 now have identical incidence and form one
canonical original-edge class. Suppressing the unlabeled degree-two source
vertex is only an explanation of this incidence equality: it is not a new
edge or a change in cut cost. Under the relabeling x4 becomes the third
active leaf, the residual family is exactly K_(N-1). The compact formulas
also show the equality directly: remove L_3,R_3 and all A rows containing3,
then identify the equal g_2,g_3 columns. Earlier subsumption again commutes
with filtering on p_3.

The reflected endpoint row has the same two transitions. At N=5 the row G
has gap branches, each discarding two endpoint labels and leaving N=3.
Consequently every recursive node with active size at least five has two
children, and each child has active size at least N-2. The remaining active
conflict family has one connected factor, so even refactoring at every node
would not remove this behavior.

## 5. Paid lower bound for one witness

Run literal SPEC-CB1 on S_(2b+1),T_(2b+1) with global budget b. There is only
one initial factor. Per-factor iterative deepening must run SEARCH at budget
b-1 before finding an optimum at b. The b-1 trial fails: selecting fewer
than b original edges cannot hit all original conflicts, as the block-size
lower bound in section1 proves. No early success can shorten this trial.

At depth d<=b-2 of that trial, at most2d active labels have disappeared.
The active size is at least2b+1-2d>=5. Section4 therefore gives exactly two
children at every internal node until depth b-1. At depth b-1 the remaining
budget is zero and the active size is at least3, so a nonempty conflict
remains and each leaf fails. The trial visits a full binary tree with

    1+2+...+2^(b-1) = 2^b-1

recursion nodes. These are failed-budget generation nodes, not outputs or
all-optimum enumeration. Each has positive paid work. Since the input size
N=2b+1 is linear in b, 2^b-1 is not bounded by any fixed polynomial factor
times (3/2)^b. The ratio has exponential factor (4/3)^b. Literal GLOBAL-CB1
therefore cannot satisfy its licensed O*((3/2)^b) generation rate.

With preorder ids the successful b trial takes b+1 nodes, and the failed
budget-t trial takes2^(t+1)-1 nodes. Summing t=0,...,b-1 and the successful
trial yields exactly2^(b+1)-1 search nodes. The lower bound2^b-1 alone
suffices, and is independent of first-success branch order.

## 6. Ordinary and reduced eligibility

Ordinary legality and original-label reconstruction are explicit in section1.
The family has no common nontrivial pendant subtree. Every proper
nontrivial pendant subtree of S_N is a suffix containing xN; every such
subtree of T_N is a prefix containing x1; equality would require the whole
label set. In particular the two cherries {x(N-1),xN} and {x1,x2} differ
for N>=4. Thus common-cherry/pendant-subtree tidying leaves the family.

For a rooted oriented common-chain definition, there is no common chain of
length at least three. Parents of any two nonsibling leaves occur in
opposite ancestor orders in the two caterpillars. Three leaves cannot all
be siblings in a binary tree, so a common ordered chain of three would
contradict that reversal. A reduction convention allowing reversal of a
rooted chain has not been imported or certified. SAFE-COVER-TARGET and its
source note do not specify the full reduction list, so eligibility for an
unspecified stronger meaning of reduced remains unclaimed. The literal
SPEC-CB1 proposal and this ordinary lower family require no such import.

## 7. Executed evidence and remaining acceptance

`results/algorithm-balanced-cover-continue-adversary-controls-v1.json` records
6 abstract controls,9 ordinary controls,26 corruption catches, and all-source-
cutset characterization checks on the ordinary fixtures. The instrument hash
and frozen design/fixture hashes are in JOURNAL-CB1-X0.md. Their controls were
executed before the new family pilots.

`results/algorithm-balanced-cover-continue-adversary-pilots-v1.json` retains
literal source/target trees, source-cut certificates and timings for matched
caterpillars m=2..7 and reversed caterpillars N=3..10. Direct partition
optimization independently verifies matched m<=4 and reversed N<=7. The
matched family measured9,31,117,459,1825,7287 total nodes; that finite sequence
has no asymptotic claim here. Reversed caterpillars measured3,3,7,7,15,15,31,31
nodes for N=3,...,10, respectively, with one factor throughout.

`results/algorithm-balanced-cover-continue-adversary-reverse-invariant-v1.json`
checks original tree conflicts against the independent triple-span formula
for N=3..13, maximal columns/minimum rows and both left-row transitions for
N=5..13, and the complete failed trials for odd N=5,7,9,11,13. The failed
trial counts are3,7,15,31,63. Eighteen deliberately omitted-column/row formula
comparisons are rejected. This took0.1002840839998953 seconds in the Python
body. `...-reverse-compact-v1.json` checks the compact K_N formula and
idempotent quotient for N=5..20; it took0.2088387920000514 seconds. These
are small measured family checks, not a new broad census or a universal
proof by finite enumeration.

The source derivation, exact quotient invariant, and full paid lower-bound
argument above require fresh nonauthor review and, under the project gate,
source-bound formalization before VERIFIED-CLOSED status. No Lean file was
created or compiled, and no axiom audit or Lean closure is claimed. No
novelty claim is made. The restricted rank-two alpha=2 proposal survives
this family; unrestricted faster algorithms and the original safe-cover
existence question remain open.
