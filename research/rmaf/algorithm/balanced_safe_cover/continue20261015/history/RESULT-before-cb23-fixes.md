# Global conflict search and two exact obstructions

The guarded-cover construction remains open. This continuation implements an
explicit original-edge conflict search, removes several redundant branches,
and records why two proposed runtime arguments fail. It establishes no
unrestricted runtime below2.3391. Algorithm, Correctness and Smaller base
remain open under the main target's acceptance standard.

## Executable proposal

CB1 constructs the conflict family of conflict/PROOF.md C1 on the original
source edges. It removes row supersets and factors the incidence graph.
Each factor is optimized once by iterative cut budgets, with dynamic
maximal-column projection and minimum-row branching. One minimum witness per
factor is sufficient; a Cartesian product of optimum choices is unnecessary.

CB2 adds repeated singleton forcing after column projection, polynomial
residual-CNF implication tests, prefix-cost branch domination, and exact
row-mask/budget caching. If prefix i costs no more than prefix j and every
row of residual i contains a row of residual j, every residual j witness
also satisfies residual i. Retaining i preserves some minimum solution.
CB3 pays to compile every remaining minimal row and chooses the least exact
mass at the preregistered alternative base7/3 with residual fraction0.
The original alpha5/4 and alpha3/2, theta1/2 targets remain unchanged.

Successful outputs are complete agreement forests. The verifier checks
original edge indices, duplicate cuts, full original source components,
original labels, rooted restrictions, target supports, nonempty components
and cut accounting. Their terminal class is all-compatible and their original
unmarked tau is0. No completion optimizer is called. Internal factor budgets
start at0 even when the supplied budget is larger than the original optimum,
so a successful output is an original optimum, conditional on C1.

C1 and its normalization argument are handwritten source-model imports,
pending their separate fresh review. The new generic finite Lean implications
do not prove C1. Direct certificate verification checks feasibility; it does
not by itself certify optimality or budget failure.

## Conditional correctness and charges

Row-subsumption preserves all transversals. Maximal-column projection can
change a transversal, but preserves its minimum cardinality by C4's
hit-preserving replacement. The selected original edge remains an original
source cut. A singleton row forces its edge in the projected system; removing
its hit rows decreases the minimum by exactly1. Branching on every edge of a
remaining row preserves a minimum transversal. Prefix dominance preserves
at least one minimum branch by the explicit row implication and cost
inequality. Exact caches identify identical original-edge constraints and
budgets; they perform no graph-isomorphism test.

Incidence factors have disjoint edge universes. Their transversal minima
therefore add: restricting any full transversal gives the lower bound, and
uniting one factor minimum gives the upper bound. Independent iterative
budgets return each exact factor minimum or prove that the unspent budget
cannot cover the next factor. C1 then identifies the combined minimum with
an original agreement-forest optimum. Normalization rules out a redundant
cut in a minimum transversal. All reconstructed components are retained;
there is no reduction history to undo and no added root label.

A recursive retained child consumes at least1 original cut. Structural
singleton closure terminates after at most2n-2 distinct edge selections.
With budget at most n-1, every search and factor deepening is finite. Calling
solve(S,T,n-1) defines an optimization wrapper because singleton agreement
forests have n-1 cuts. Validation failures and certificate invariant failures
are explicit exceptions; no such failure occurred in the pinned controls.
The source-model proof, implementation correspondence and fresh review must
be completed before claiming universal exactness.

Every state includes paid row simplification, column comparisons, child
closure, implication tests, hashing, exact rational mass arithmetic and
serialization. Original H has polynomially many rows and edges. These
operations are polynomial per state; the number of states remains open.
A maximum retained branch rank d gives a coarse O*(d^b) search bound.
Factor count and iterative budgets contribute polynomial factors. CB2/CB3
cache size is also charged. No local-distance recognition is hidden in this
proposal. Full-cut binomial enumeration is unnecessary here, but no licensed
constant generation bound follows from that fact.

## CB1 connected lower family

A fresh child constructed opposite-order rooted caterpillars on N=2b+1
labels. Every rooted triple disagrees, so an agreement block has at most two
labels. Consecutive pairs and one singleton attain exactly b cuts. The
original conflict incidence system is connected. Its maximal-column quotient
has two-edge minimum rows that, under the actual CB1 branching, leave the
same family with active size N-2 or N-1.

At the failed budget b-1 trial, every node through depth b-2 still has at
least five active labels and exactly two children. Every depth b-1 leaf has
a nonempty conflict and budget0. The trial therefore has2^b-1 nodes. With
N linear in b, this excludes O*((3/2)^b) for literal CB1, independently of
all-optimum enumeration or disconnected products.

The full source derivation and exact quotient invariant are in
adversary/REVERSE-CATERPILLAR-LOWER-BOUND.md. Its author executed independent
controls and small family checks. The asymptotic argument is handwritten;
formal source-model verification and a further nonauthor review remain
pending. The family has no common nontrivial pendant subtree; stronger
reduction conventions are qualified explicitly. This lower bound applies
to CB1, not automatically to the later CB2/CB3 operations.

## All-row recurrence obstruction

The original ordinary six-leaf pair is

    S=(((((a,b),c),d),e),f),
    T=((a,c),((b,e),(d,f))).

Its frozen optimum is3. It has no common nontrivial pendant clade. The exact
reduced conflict system has26 minimal rows. CB2's first-row rule retains four
unit-cost children. CB3 compiles every one of the26 rows; each retains at
least three unit-cost children after singleton closure and residual-CNF
prefix domination. The best row is mask960, the original span of {a,b,c}.
Its retained branches cut pendant c, pendant a and pendant b, each costing1.
At base7/3 its exact mass is9/7. Every other row has mass at least9/7.

Consequently the specified one-row uniform cut-budget recurrence cannot
have a base below3 on this source-realized state. The failure is at
choose_row's required mass<=1 call. It rejects a recurrence certificate,
not correctness, global amortization, larger multirow macros, different
constraint representations, or the original guarded-cover existence target.
The full original trees, edge indices, conflict causes, all26 candidates,
retained cuts and exact masses are preserved in
algorithm-balanced-cover-continue-cb3-obstruction.json.

## Executed checks and scope

CB1:6 abstract and9 ordinary fixtures passed, with37 corruptions rejected.
CB2: the same fixtures plus structural controls passed, with41 corruptions
rejected. CB3: those literal optimum fixtures and new all-row controls passed,
with42 corruptions rejected. Each harness also checks insufficient-budget
failure, larger-budget original-optimum return, and production calls with
partition/packing/test oracles disabled. The tree primitives and finite
scoring oracle share GLOBAL-C code, so these are production-side checks.

The CB2 Lean audit replays8 scoped finite/list/arithmetic statements and
rejects2 false propositions. The CB3 audit replays7 literal-profile and
arithmetic statements and rejects1 false proposition. Retained isolated
compiler inputs, source hashes, logs and axiom reports contain only standard
propext/Quot.sound where printed. The actual source extraction of all26
profiles is not formalized by those literal-list theorems. No full safe-cover
or universal search bound is asserted.

CB2's first control receipt overcounts wall time by adding the nested harness
duration twice. The original receipt and script are preserved; the corrected
control receipt is algorithm-balanced-cover-continue-cb2-controls-v2.json.
This metadata repair changes no optimum, branch, corruption or mass result.

## Exact remaining theorem

For the original Section8 target, construct oracle-free globally guarded
partial original cut certificates in total O*(alpha^b) size and time, with
alpha5/4 or prelicensed3/2, preserving an ORIGINAL optimum and certifying the
terminal class and original unmarked tau<=b/2 for every output. Rejected
certificates, every witness construction and failed budget must be counted.

For the full-certificate proposal above, the missing replacement is a
source-model global charging or state-compression theorem bounding all paid
reachable residual states at a base below2.3391. A theorem that merely
chooses the best single row after the implemented closure/domination is
false on the retained six-leaf pair. A connected2^b family also defeats
CB1's licensed3/2 bound. Neither obstruction is a complexity lower bound
for ordinary rooted MAF or for guarded-cover algorithms.
