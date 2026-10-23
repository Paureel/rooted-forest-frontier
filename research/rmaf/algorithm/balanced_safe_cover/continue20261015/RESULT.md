# Global conflict search and two exact obstructions

The guarded-cover construction remains open. This continuation implements an
explicit original-edge conflict search, removes several redundant branches,
and records why two proposed runtime arguments fail. It establishes no
unrestricted runtime below 2.3391. Algorithm, Correctness and Smaller base
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
mass at the preregistered alternative base 7/3 with residual fraction 0.
The original alpha=5/4 and alpha=3/2, theta=1/2 targets remain unchanged.

Successful outputs are complete agreement forests. The verifier checks
original edge indices, duplicate cuts, full original source components,
original labels, rooted restrictions, target supports, nonempty components
and cut accounting. Their terminal class is all-compatible and their original
unmarked tau is 0. No completion optimizer is called. Internal factor budgets
start at 0 even when the supplied budget is larger than the original optimum,
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
its hit rows decreases the minimum by exactly 1. Branching on every edge of a
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

A recursive retained child consumes at least 1 original cut. Structural
singleton closure terminates after at most 2n-2 distinct edge selections.
With budget at most n-1, every search and factor deepening is finite. Calling
solve(S,T,max(0,n-1)) defines an optimization wrapper because a nonempty singleton agreement
forest has n-1 cuts, and the empty input costs 0. Validation failures and certificate invariant failures
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
a nonempty conflict and budget 0. The trial therefore has 2^b-1 nodes. With
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
projected conflict system has 26 minimal rows. CB2's first-row rule retains four
unit-cost children. CB3 compiles every one of the 26 rows; each retains at
least three unit-cost children after singleton closure and residual-CNF
prefix domination. The best row is mask 960, the original span of {a,b,c}.
Its retained branches cut pendant c, pendant a and pendant b, each costing 1.
At base 7/3 its exact mass is 9/7. Every other row has mass at least 9/7.

Consequently the specified one-row uniform cut-budget recurrence cannot
have a base below 3 on this source-realized state. The uniform recurrence proof requires mass<=1 at choose_row; its
returned minimum violates that obligation. The executable search continues
when the mass exceeds 1. It rejects a recurrence certificate,
not correctness, global amortization, larger multirow macros, different
constraint representations, or the original guarded-cover existence target.
The full original trees, edge indices, conflict causes, all 26 candidates,
retained cuts and exact masses are preserved in
algorithm-balanced-cover-continue-cb3-obstruction.json.

## Executed checks and scope

CB1: 6 abstract and 9 ordinary fixtures passed, with 37 corruptions rejected.
CB2: the same fixtures plus structural controls passed, with 41 corruptions
rejected. CB3: those literal optimum fixtures and new all-row controls passed,
with 42 corruptions rejected. Each harness also checks insufficient-budget
failure, larger-budget original-optimum return, and production calls with
partition/packing/test oracles disabled. The tree primitives and finite
scoring oracle share GLOBAL-C code, so these are production-side checks.

The CB2 Lean audit replays 8 scoped finite/list/arithmetic statements and
rejects 2 false propositions. The CB3 audit replays 7 literal-profile and
arithmetic statements and rejects 1 false proposition. Retained isolated
compiler inputs, source hashes, logs and axiom reports contain only standard
propext/Quot.sound where printed. The actual source extraction of all 26
profiles is not formalized by those literal-list theorems. No full safe-cover
or universal search bound is asserted.

CB2's first control receipt overcounts wall time by adding the nested harness
duration twice. The original receipt and script are preserved; the corrected
control receipt is algorithm-balanced-cover-continue-cb2-controls-v2.json.
This metadata repair changes no optimum, branch, corruption or mass result.

## Guarded partial frontier

CB4 uses the same global constraints to emit partial original-edge certificates
before the full search finishes. At each actual prefix C it checks original
components and terminal geometry. Compatible components use their whole
restriction as a local witness. Other components use greedily chosen pair
paths disjoint in both original trees, with remaining labels singleton.
Connected-support expansion realizes each local partition with exactly
pieces-1 original internal cuts. These are explicit local upper witnesses;
no distance optimizer is called.

A prefix is emitted only when it is nonredundant, terminal, within budget,
and every local witness costs at most floor(b/2). Every emitted certificate
records original source vertices, target supports and actual local original
cuts. Guarded stopping preserves a minimum path under the same explicit
C1/C4 and branch-dominance arguments. At worst a full normalized optimum
passes with local cost 0. Geometry depends on C, so the visited-state key
includes the original precut mask; CB4 does not discard distinct forests
merely because their residual conflict rows agree.

Five known guard controls, nine ordinary fixtures at two budgets each, and
five cost/label/support/duplicate corruptions passed. Each tested budget
cover retains an original optimum, and every emitted certificate passes the
literal graph/witness checks. Production generation ran with scoring oracles
disabled. A fresh independent instrument confirms all 18 covers and all 24 emitted
certificates, including actual local distances and original internal cuts.
It checks 108 retained substitutions at 15 compiled nodes. The path invariant
is existential: other visited states can exclude every original optimum.
Prefixes 65 and 257 of the quotient-star run require total cost 4 versus
original optimum 3; SPEC-CB4-ERRATUM-v2.md preserves these exact witnesses
and corrects the overstrong wording in the frozen pin. The corrected coverage
argument is conditional on the stated source imports. The total frontier
size/time bound remains open. The
separate terminal-completion imports remain open at the algorithm consumer.

## Exact remaining theorem

For the original Section8 target, construct oracle-free globally guarded
partial original cut certificates in total O*(alpha^b) size and time, with
alpha=5/4 or prelicensed3/2, preserving an ORIGINAL optimum and certifying the
terminal class and original unmarked tau<=b/2 for every output. Rejected
certificates, every witness construction and failed budget must be counted.

For the full-certificate proposal above, the missing replacement is a
source-model global charging or state-compression theorem bounding all paid
reachable residual states at a base below 2.3391. A theorem that merely
chooses the best single row after the implemented closure/domination is
false on the retained six-leaf pair. A connected2^b family also defeats
CB1's licensed3/2 bound. Neither obstruction is a complexity lower bound
for ordinary rooted MAF or for guarded-cover algorithms.

Fresh CB2/CB3 source review reconstructs all 26 causes and all 26 row costs,
independently checks optimum 3 and all 1024 source cutsets, and confirms the
recurrence-only obstruction. It also motivates the empty-wrapper correction
and the closure clarification above. Its frozen fixed-point interpretation
and post-contact literal stop-mode replay are distinguished in REVIEW.md.
