# An exact ordinary rooted agreement-forest algorithm with a 2.33 exponential bound

## Status and requested review

This is an expert-review submission of a complete mathematical argument, supported by included Lean component proofs. The claim is an exact algorithm for ordinary rooted binary Maximum Agreement Forest, with complete cost O*(2.33^k) on the specified log-cost RAM, where k counts optimum components. Two fresh agent contexts reviewed the assembled mathematical argument after their own controls and initial analyses. Their confirmation is relative to shared formal dependencies. No external human review, new whole-runtime Lean theorem, certified numeric executable, practical-speed result, or novelty claim is asserted.

The readable proof below and its electronic appendices form one self-contained review package. The appendices include the full finite procedure definitions, exact proof-bearing field types, detailed mathematical operation/size arguments, and the project Lean sources needed by the stated component theorems. They are supplied rather than treated as unproved hypotheses. Standard Lean 4.35.0 libraries and its trusted kernel are external software prerequisites only for an optional clean rebuild. Reading the mathematical argument requires no software installation, network service, prior chat, original workstation path, or author-supplied answer oracle.

The main text identifies the actual remaining trust boundary: the complete runtime correspondence and cost assembly are mathematical proofs; not every step has been formalized. The formal component proofs and final agent reviews share source lineage and a Lean engine. A plausible error in a shared component, its binding to the intended definition, or the mathematical bridge would not be excluded merely by two agreeing reviews. Reviewers are asked to examine those connections, not to accept the internal completion label as evidence.

## 1. Objects, conventions and exact theorem

A tree is a finite full binary rooted tree with natural-number leaf labels. The left/right order is representational: rooted labeled isomorphism may swap children independently at any vertex. A proper pair T,S has duplicate-free leaf lists with the same labels. Let N >= 1 be their common number of leaves, and let L >= 1 satisfy x < 2^L for every original label x. A smaller input alphabet can be injected into these natural labels without changing the combinatorial problem.

For a nonempty set of labels B, T|B is the rooted restriction: retain the paths connecting B, root at their least common ancestor, and suppress unary vertices. Its minimal embedding in T includes every intervening original path vertex, including vertices suppressed in T|B. An agreement forest is a partition F=(B_1,...,B_j) of the common labels into nonempty blocks such that T|B_i and S|B_i are rooted labeled isomorphic for each i, and the minimal embeddings of distinct blocks are vertex-disjoint in each original tree. Block and label-list order may be retained operationally but do not change feasibility. The objective is to minimize j. There is no added root, stem leaf or rho taxon.

This is the ordinary edge-cut convention. To check the correspondence, cuts producing components give disjoint connected minimal embeddings, so their induced partition satisfies the definition. Conversely contract the pairwise disjoint minimal embeddings in one input tree. In the remaining tree, extend these contracted marked vertices to connected zones, assigning each unmarked vertex to a nearest marked vertex, resolving distance ties by one fixed order. A shortest path to the assigned mark remains in its zone: a competing closer or earlier tied mark at an intermediate vertex would also beat that assignment at the original vertex. All leaves already belong to a marked embedding. Cutting the edges between zones therefore gives exactly j nonempty labeled components and j-1 distinct original nonroot cut edges. Suppression yields the restrictions. Apply this in both trees. The included recovery proof supplies the algorithm's specific original S cuts, rather than relying only on this existence argument.

Write k for the optimum component count and Q=k-1. Singletons are feasible, so 1 <= k <= N and Q < N. The program is not supplied k or Q. They are analysis parameters. Replacing components by cuts in the headline without this conversion would change the statement.

**Theorem.** The finite implementation specified by the included procedure appendix, the exact operational projection, and the canonical input convention terminates on every canonical finite tree-pair code. On a proper pair it returns a globally minimum agreement forest and distinct valid nonroot cut edges in the original S realizing it. On an improper decoded pair its specified preflight returns absence with no optimizer trials or recovery calls. For proper input its complete actual log-cost RAM bill satisfies

```text
RAMCost(T,S) <= A(N,Q,L) * (Sopt(T,S)+1)
            <= A(N,N,L) * (P(N,L)+1) * (233/100)^k.
```

P and A are the explicit fixed polynomials in Sections 8 and 10. In particular the cost is O*(2.33^k), where the suppressed factor is polynomial in N and original label width L. Total allocated memory need not be polynomial. No claim about a physical CPU, bit-tape machine, unfinished numeric listing, current best known bound, or usefulness of the loose constants follows.

The canonical entry has only U(T,S), an injective packed natural encoding of the pair, in register 8; every other register, including register 4, is zero; the heap is empty. QUERY_WORD(U,q) is a different entry whose analysis retains its actual supplied q. The optimization theorem does not silently ignore or copy an arbitrarily large independent budget word. Arbitrary corrupted heaps and invalid raw codes are outside the canonical tree-code premise; the displayed parser has finite fault branches for invalid codes. No optimum, successful execution, word-width promise, cost, graph, source counter or answer is an input.

## 2. Complete algorithm specification

The exact algorithm is fixed by `algorithm/ALGORITHM-v1.md`, the code/data declarations in `algorithm/PROCEDURES-v1.md`, and `algorithm/PROJECTION-AMENDMENT-v2.md`. These are finite definitions, not calls to unspecified mathematical oracles. `algorithm/DECLARATIONS-v1.txt` indexes every declared procedure and origin. Where a high-level name occurs below, its full body is in that appendix. The representation, evaluation order and primitive costs are fixed by `algorithm/REPRESENTATION-AND-OPERATIONS-v1.md` and the elementary realization proof in the mathematical appendix. The following entry/scan equations are the complete outer control.

```text
OPTIMIZE(T,S):
    p := proper(T,S)
    labels := leaves(T)
    fuel := length(labels)                 // evaluated also if p=false
    if not p: return (no_selection, None, [])
    search := SCAN(T,S,0,fuel)
    if search.selected=None: return (search,None,[])
    (q,F) := search.selected
    recovered := RECOVER(S,F)              // one eager call
    return (search,recovered,[(F,recovered)])

SCAN(T,S,start,0): return (None,[])
SCAN(T,S,start,fuel+1):
    answer := QUERY(start,T,S)
    if answer=Some(F): return (Some(start,F),[(start,answer)])
    tail := SCAN(T,S,start+1,fuel)
    return (tail.selected,(start,answer)::tail.trials)

PAID(parentBudget,T,S,r):
    if r < parentBudget: return QUERY(r,T,S)
    return None
```

QUERY executes its properness and pretest, then the exact priority-ordered Early selection. Its branches are stop/refused, common reduction, one-pendant reduction, high-pendant reduction, forward/reverse Rule4, and Hard2. COMMON alone may invoke an ordinary child at the same budget, and only after an actual strict decrease of target leaf count. Other ordinary child entries use PAID. Forest calls use their own finite forest-budget/list recursions and fixed PAID adapter. Every applicability test and fallback is in the procedure appendix.

Rule4 has three generated branches. Its actual tail-first answer routine computes the branch state before the affordability test. Even an unaffordable branch therefore pays that state construction. Full-output routines are likewise tail-first. A selected-child list runs each affordable forest and the whole tail even after a failed forest. A scheduler instead stops at its first failed hard job. These are different code paths; equal returned forests do not justify interchanging their evaluation order.

Hard2 distinguishes a literal disjoint route from the paid-output route. The disjoint route constructs and checks its partition, may call Rule5 on the actual two-good case, or runs its disjoint-parent specialization. The paid route selects Empty, Good, Hard or Bad, executes that paid arm, and then executes the unit-child combination regardless of whether a paid answer already exists. The Bad arm keeps its actual orientation test and selects either the local BothBad routine or the grouped routine. No route obtains an optimum by exhaustive partition search. The small exhaustive solver present in an early semantic module is not a runtime subroutine of this algorithm.

Rule5 repeats its actual classifier and selected builder where the code requires it. The prefix, first and third selected cases run their concrete selected children; the one case uses the common split; the second case runs the literal paid builder. Builder refusal is an actual branch. Full Setup and LiteralGeometry propositions are not input certificates: their computational data come from the executed restrictions, incident-edge tests, options and ordered guards. Their complete field types are included, and Section 4 explains why the executed tests supply their proof fields.

RECOVER runs its input check and, on success, completes the full eager RW generator before taking the head output. It retains its source-cut/output/refusal data. Its raw generator is different from the plain CoreProgram generator used in some forest routines. A same-name or equal-value substitution between them is not part of the implementation.

## 3. Semantic primitives and functional correctness

The checker `agreement T S F` is exactly: both nonempty-partition checks; every block's restricted-tree isomorphism; and pairwise minimal-embedding disjointness in both trees. `sameShape` evaluates the straight and crossed child pairings; its formal `sameShape_correct` theorem identifies it with inductive rooted labeled isomorphism. `restrict` suppresses unary nodes. `minimalVertices` keeps the unsuppressed original paths beginning at the selected least common ancestor. Thus the checker implements Section 1, rather than a topology-only surrogate that can accept overlapping embeddings.

The component functional proof is included in `formal/`, with a context map in `formal/CONTEXTS.json`. Its assembly is `CompletedFunctional233.query_correct` in WholeFunctional.lean. For proper T,S and any natural q it proves QueryExact for the actual canonical FastOrdinary.solve: every returned forest is feasible within q+1 components, and every feasible forest within that budget has a surviving successful answer of no greater size. The final theorem has no outstanding local-rule or Rule5-survival parameter. Its malformed companion proves refusal on false properness.

The ordinary proof is well-founded on the lexicographic pair (q, number of leaves of the first input). Local soundness checks validate reconstructions; cover lemmas show that an optimum survives the selected reduction or branch. The formal local rules supply common, one, high, forward Rule4 and reverse Rule4. `actual_rule5` supplies the previously missing disjoint clause from the included G0 exchange theorem; `actual_disjoint` and `actual_hard2` pass it to the original Hard2 caller. `ConditionalQuery.lean` then instantiates the actual generated induction with these inhabitants and the impossible-rejection lemma. This is the specific caller composition; proving a generic geometry theorem alone would not discharge it.

For clarity, G0's exact conclusion for actual LiteralGeometry data D and any agreement forest G is: there exist child in guardedPlan(D) and H such that agreement(T,S,H), |H| <= |G|, and Refines(H,child.partition). Its proof is the included G0Native.lean, not a remaining hypothesis. Its main partition analysis separates b singleton, a and b shared, a singleton, and the exceptional crossing configuration. The shared-block case refines by the two pendant arcs; single-edge splitting adds at most one component; the exceptional cases build the actual target-guarded type-I/type-II/fallback partitions. Nonempty-piece counting and the component exchanges pay every introduced split. The final `generic_g0_survival` composes these cases. An expert can audit that substantial proof directly; the short case description here is not offered in place of its proof terms.

Finite scan induction gives trials at budgets 0,1,... until the first Some. A singleton partition bounds a successful budget by N-1. QueryExact makes every earlier failure exclude every smaller optimum. The selected q is therefore k-1. The included `optimization_correct` theorem also proves a single successful original-cut recovery, distinct valid original nonroot source edges, and the exact failed-trial and recovery lists. The separate outer value correspondence in Section 5 is needed before transferring these canonical conclusions to the mathematical RAM implementation.

## 4. Actual execution, guard evidence and termination

The main runtime bridge is a simultaneous induction, not a declaration that an accounting trace equals execution. Fix an ordinary parent rank (q,leaves(T)). Define R(U,V,r,a) to mean that the actual smaller QUERY evaluation completes with answer a. Ordinary induction supplies both existence on enabled smaller calls and equality with the canonical answer, including malformed and None-returning children. No child properness or successful answer is required to construct the execution.

Inside one parent, strong induction on forest budget handles overlap recursion: the actual eligibility check 1 <= cutCount <= b gives b-cutCount < b. Branch, scheduler, output, entry, child and request recursions are structural on their actual finite lists. Raw generation has its actual finite fuel and structural tree recursion. A scheduler's failed hard head stops its tail; an answer-list routine may continue despite failure. COMMON uses its observed strict target-leaf test at equal q; all other ordinary terminals pass PAID's r<q check. These facts construct finite actual evaluations on arbitrary finite trees before restricting to proper-root cost domains.

At each taken branch construct the corresponding graph from the actual option/Boolean discriminator and the actual completed subevaluations. Also construct an exhaustive chronological word of callback attempts. A disabled PAID attempt has live=false and no QUERY body. An enabled call returning None has live=true and an actual body. Concatenation follows physical evaluation order and offsets by all attempt positions, including refused attempts. The four ordinary terminal sites are direct COMMON, forest singleton, the raw scheduler's hard-pair adapter, and common paid jobs; all other named callbacks forward to these or to FOREST. The full callsite/constructor census is `mathematics/DYNAMIC-ADEQUACY-CENSUS-v1.md`.

The proof-bearing constructors require real guard evidence. For Rule4, successful Priority gives label properness, no common cherry and no one-pendant reduction in either orientation; LocalGuard gives the two ordered cherries and the exact two-cut/subtree conditions. Setup's two partitions are proper, nonempty complements. Its selected minimal embedding is connected. If it has exactly one incident crossing edge, deleting that edge shows that the embedding is one entire side: a missing vertex on that side would create another boundary along its unique path. The descendant subtree consequently has X or its complementary Y leaves. This supplies the required disjunction, including the root-containing side; an X-only inference is invalid. Nonemptiness, restrictions and maximum-label arithmetic supply the other Setup fields. LiteralGeometry's successful subtree/address options and seventeen actual predicates supply all eighteen propositions; endpoint order is the specified two-orientation disjunction, not a presumed sort. Failed tests refuse or continue the finite search as printed.

For fixed R that is functional in its returned answer, every fixed-input graph has unique computational result/slot/occurrence data. Prove this by scheduler-list induction, forest-budget plus branch-list induction, then structural induction over the remaining acyclic graph families. Actual options, affordability and route tags separate incompatible constructors. Only proof fields use proof irrelevance. This identifies the existential RouteLedger from a conditional source interface with the particular RouteLedger just constructed from actual evaluation. Existential ledger existence by itself would not justify that identification. The full constructor proof is the required DYNAMIC-GRAPH-DETERMINISM appendix.

Only now apply the included exact graph-to-source/permutation/slot interfaces. Distinct composite labels preserve duplicate equal query tuples. Their position maps send every live ordinary body to a distinct stored SOURCE position, preserving target, source, budget and answer. Prefix local positions with the parent's address for a global injection. The map need not be surjective: stored refused or auxiliary source positions may overcount. Rule4/full-output tails precede heads, paid precedes units although recording units++paid, and disjoint children precede their query. These are explicit tagged permutations, never a false physical-order equality.

## 5. Operational projection and outer value transfer

The mathematical implementation removes accounting-only work/debit/fee arithmetic and the exact propagation-only fields listed in its projection. It additionally removes precisely Built.coloring and InitialMeasured.coloring under the v2 amendment. Actual Group.color and every value-producing color computation remain. The one accounting frontier replay and its ordinaryCalls propagation are removed only in the named two record families; their actual answer-producing FOREST remains. All other metadata, checks, calls, queries, visits, failures, retained traces and producers are kept and charged.

A structural noninterference induction over the complete accounting read-site inventory shows that these omissions affect no retained decision, callback argument/order, answer or decoded output. A removed argument to a pure bump does not remove a value-producing second argument. Repeated classifiers/builders and eager alternatives remain repeated. Raw FOREST's runtime Receipt has answers/calls/visits; its larger graph MeterReceipt adds auxiliary query observations. That type distinction is not permission to erase runtime query fields of the source/grouped schedulers.

Combined with Section 4, each actual QUERY returns the canonical solve value and preserves every declared retained field. Finite SCAN fuel induction then identifies the entire ordered optimizer history using the included unconditional primitive preflight/scan/recovery VALUE theorems. The RECOVER value theorem is used only after noninterference and the actual eager recovery execution are established. The chosen result and recovery-history record share its single returned reference. These steps transfer Section 3's optimum and original-cut conclusions to the specified mathematical implementation.

## 6. Local operation credits

Count abstract operations U before elementary lowering: scalar actions, actual field accesses, cons emissions, comparisons, control and paid call/return handling. A parent count excludes only recursive ordinary QUERY bodies, counted once in their own derivations. Calls to helpers, FOREST and generators are not free. For original proper input, source-membership and the exact reached-domain theorem preserve both child leaf counts <=N and budgets <=Q. This is not the false restriction q <= the current reduced leaf count.

Put a=N+1. The finite payload catalogue counts path cells, tree/list/record constructors, all job forests, merge Cartesian-product payload and simultaneously constructed predicate environments. The corrected sum is at most 108400 a^3. The largest environment bound uses

```text
296 a^2 + 3416 a + 160 <= 2048 a^2       (a>=2).
```

The difference is at least 88a-160 >=16. Thus D'=2^18 a^3 bounds the finite payload envelope. It does not bound exponential output/query/refusal spines. Let P'=2^48(D'+1)^10. The seven included finite recipe rows bound all repeated restrictions, hulls, shape tests, embeddings, checks, DP, merges and guards by this polynomial envelope, with their exact loop products and field costs.

The plain generator induction gives work >=256*visited + copied-left-spine + pruned, and attempted children <=2*visited. Zero-work refused attempts are paid by their enclosing visit. All repeated equal output/refusal cells are charged by occurrence. The distinct eager RW generator keeps its contains/erase, both cut attempts, all outputs and literal append-length bills even before or after refusals. Forest strong induction pays both raw generators, every branch materialization, every eligible child and final checks. Its active maximum includes the formerly omitted 2^30 term:

```text
16*max(2^30,2^22*(m+1)^3,2^18,2^16) <= 2^34*(m+1)^3.
```

At the outer forest m<=8a this is <=2^44 a^3. Rule4 has a separate bound 2^30 a^5 for its exactly three eager state constructions and finite builder/guard/selection work, including unaffordable states whose returned source branch omits state.work. Positivity of an assigned work field is not used as an operation proof.

There are five explicit outer incidence channels, each bounded by a distinct-position injection into the selected local debit expression d=completeLocalDebit:

| Channel | Actual charged occurrences |
|---|---|
| G | Full work of each reached eager generator, including probes and actual nil-triggered regeneration; reference reuse does not generate again |
| F | Outer FOREST invocations through the exact alternative child/Rule4/full-output/current/call-debit interfaces; their internal generation is not charged again here |
| V | Every entry/output/selection iteration, including None, refusal and duplicate heads |
| A | Every unbounded append's copied left spine, using its literal length summand |
| Qmap | The grouped arm's separate complete query-list conversion |

The inequalities G,F,V,A,Qmap <=d are separate; their numeric credits may overlap across channels. At most sixteen additional finite P' recipes pay administration. Therefore

```text
Ulocal <= P'*(G+F+V+A+Qmap)+16P' <=64P'*(d+1).
```

All channel injections, generator recurrences, finite recipes and payload calculations are supplied in the detailed mathematical appendices. Their original insufficient coefficient and omitted maximum are preserved in historical records, but the active proof includes the explicit arithmetic-v3 and maximum-v4 corrections.

## 7. From actual calls to the full source counter

The analysis recurrence is

```text
C(q,T,S) = d(q,T,S) + sum over ALL attached source query positions p of C(p).
```

Attached positions distinguish equal tuples. Its well-founded rank is the included source lexicographic descent theorem; C is not executed as a runtime fee oracle. Inspection of the actual front debit gives d>=2. Hence local work <=128P'd.

Induct on the source rank. Decompose actual operations into local work and each actual recursive ordinary body. Section 4 injects those bodies into distinct stored positions. Apply the child bound at its corresponding position, then enlarge the nonnegative sum from the image to every source position. Thus Uquery<=128P'C. Neither equality of recursion trees nor deletion of failed/refused stored calls is asserted. Their executed local comparisons remain paid.

Summing the actual optimizer trials and its positive preflight/scan/finish/one-recovery terms yields Uopt<=256P'(Sopt+1). Since D'+1<=2^19 R^3 for R=N+Q+L+2, P'<=2^238 R^30. Therefore

```text
K=2^252 R^32,             Uopt<=K*(Sopt+1).
```

This operation bound precedes machine instruction counts and fees. It includes every failed budget and does not assume that the first successful call alone pays the scan.

## 8. The exact source exponential theorem

The included `ExplicitSourceOptimizer20261022.optimum_k_source_bound` proves for the same proper original trees and original-label bound that the literal sourceOptimizeMeter value is the canonical optimizer and

```text
Sopt <= P(N,L)*(233/100)^(k-1).
```

The coefficient is exactly the following finite arithmetic definition. Every named polynomial is defined in the included formal source dependency closure, with scalar views in `interfaces/SOURCE--SCALARS-BASE-v1.json` and `interfaces/RELATION--PURE-SCALAR-AND-RELATION-DEFINITIONS-v1.json`; `READING-MAP.md` resolves the historical names:

```text
P(n,L) = n * ((outerJoinedPolynomial(n,n,L)
             + disjointRunPolynomial(2*n+3)
             + badPairLocalPolynomialExpression(2*n+3,n)
             + 32*(2^50*(2*n+3+n+2)^8)) * 1024*(n+1))
         + 512*(2*n+1)^2 + 64*(recoveryEnvelope(n)+32).
```

The finite arithmetic dependency graph has nonnegative coefficients and degree at most sixteen. The exact rational base is 233/100. The source proof includes local branching/generation payments, all optimizer budgets and one recovery. Fourteen affected source support lemmas were rebuilt against the completed functional query theorem rather than relying on the earlier whole-solver correctness shortcut; the supplied dependency audit records the forbidden old roots and standard-axiom closure. Those audit records are support, not a substitute for the included proof terms.

This source theorem alone is not a RAM running-time theorem. Sections 4-7 and 9-10 are the additional actual execution, operation, size and fee arguments. The comparison is to this one exact source provider; similarly named definitions from another source/object pool are not merged.

## 9. Elementary realization, input decoding and value envelopes

Values are immutable unpadded cons/constructor records. Field projection follows actual cons tails; append copies its first spine; structural equality traverses data; call/return versions of activations are allocated and retained. There is no free host stack, bulk allocation or uncharged record lookup. The fixed finite dispatch and allocation-free scalar bit loops use the published thirty-two-register natural-word machine. Fixed products use shifts/additions. Every repeated operand and actual address is charged.

For w(x)=max(1,bitLength(x)), representative fees are COPY=1+2w(x), ADD/TSUB=1+w(x)+w(y)+w(z), READ=1+w(address)+w(heapBound)+2w(value), and WRITE=1+w(address)+w(oldBound)+2w(value)+w(newBound). CONST, comparisons, shifts, Booleans, branches, jumps, halt and fault rows are all in the representation appendix. No multiplication, set oracle, inductive proof evidence, bulk memory or type-checking primitive is silently added.

The elementary construction gives fixed constants

```text
f=735030, c=367508, F=9f=6615270,
gamma=9f^2+63f+3c+62=4862469317576, s=3f+c+128=2572726.
```

Each started abstract operation allocates at most F words, independently of word width. Bit loops allocate no words per scanned bit. Given boundary width B, its finite expansion has at most gamma(B+1) instructions with internal footprint widths <=2B+3, and total bill <=16gamma(B+1)^2. The large constants are uniform syntactic envelopes for this fixed program, not machine input or practical performance estimates.

The input encoding has postorder leaf/node tokens, unary width headers and label payloads, two tree boundaries and a high sentinel. For total leaf occurrences n and summed original label widths Jlabel, it has 5n+2Jlabel digits. A digit/postorder/stack induction consumes each digit once and reconstructs both exact trees, proving safe pop/record-start/ownership conditions from the empty heap. Its raw word width is at most D0=10N+4NL+1. Popped cells and retired frames remain allocated. Nil's first emission is a separate one-word base with fee 12 before the record invariant. A direct initialization count and fee bound are

```text
Uinit=512*(D0+1); H0=1+F*Uinit;
Vinit=D0+Q+H0+f+c+8; I=16gamma*Uinit*(Vinit+1)^2.
```

The input state and successful canonical decoding are conclusions of this proof, not EntryRep premises supplied by a caller. Optimization's input budget is fixed zero; Q bounds its internally computed trials only.

At any main execution prefix with U counted operations, heap frontier H<=H0+F*U. Independently, an induction over the included complete scalar catalogue gives every persisted semantic nonpointer word x the bound

```text
D=D0+L+2*(Q+N)+s+16,
x <= 2^D + 16*s*R^4*(U+1)^4.
```

Original/fresh labels are bounded by original maximum plus twice the number of actual fresh-label events. Region/tagged colors, DP owner indices and recovery labels have different proved classes. Receipt counters count disjoint actual subevents; combining does not consume one saved receipt twice. Weighted scheduler sums have actual length/reset-count bounds and do not repeatedly aggregate previous aggregate fees. The ten retained multiplication sites have fixed 2/3/4 factors. Fixed-budget-three probes and recovery's pre-cap length are covered separately. Pointer words are classified by allocation, not mistaken for such semantic scalars. These invariants precede time/width bounds.

## 10. Explicit global polynomial and the 2.33 conclusion

Use Section 7's U<=K(Sopt+1) and Section 8's Sopt<=P*(233/100)^Q<=P*4^Q. Define fixed input polynomials

```text
Jheap=H0+F*K*(P+1)
Z=16*s*R^4*(K+1)^4
Tbig=Z*(P+1)^4
Bword=D+Tbig+Jheap+10*Q+4
A(N,Q,L)=I+16*gamma*K*(Bword+1)^2.
```

Because Sopt+1<=(P+1)4^Q, the actual heap satisfies H<=Jheap*4^Q, so address/frontier width <=Jheap+2Q+1. Also U+1<=(K+1)(Sopt+1); Section 9 gives x<=2^D+Tbig*4^(4Q), so semantic width <=D+8Q+Tbig+2. Bword dominates both at every prefix, including partially emitted records. Exponential allocation is permitted; its address width is polynomial. Neither desired RAM time nor polynomial total memory was used to derive allocation or scalar sizes.

Apply the elementary actual-fee bound only after this width derivation and sum actual operation expansions. Including initialization,

```text
RAMCost <= I+16*gamma*(Bword+1)^2*U
        <= A(N,Q,L)*(Sopt+1).
```

The polynomials have nonnegative coefficients in Q. Functional correctness gives Q=k-1<N; therefore replace Q by N in A and use (Sopt+1)<=(P+1)(233/100)^Q. This proves the theorem. Loose degree bounds are deg(P)<=16, deg(A)<=424 and deg(A(P+1))<=440. No exponential factor is hidden in N or L. The polynomial is intentionally not optimized, and this argument does not establish a practically competitive implementation.

## 11. Assumptions, proof status and verification limits

The mathematical hypotheses are exactly finite full binary rooted trees, proper common distinct labeling for the optimum claim, the original label-width parameter, canonical input state, and the published log-cost RAM semantics. There is no unproved Rule5 survival hypothesis, desired execution graph, successful-child premise, positive-payment oracle, counter equality or polynomial-memory promise. Invalid decoded pairs and disabled/failed callbacks have their displayed finite branches.

The formal component theorems have recorded Lean checks with propext, Classical.choice and Quot.sound; no problem-specific axiom is advertised as a replacement for an open lemma. The packet includes their actual source proofs and dependency contexts. The main mathematical execution/operation/scalar/fee composition has not been transformed into a single Lean theorem. Rebuilding the component corpus would test the included formal terms, not formalize the prose bridge automatically.

The two final agent contexts authored none of the candidate, saw no peer findings, executed their own prospective positive/planted controls, sealed their own initial computation reconstructions, and only then received the proposed proof arguments. They inspected full conditional theorem statements and their use-site premises. They did not independently rebuild every component proof/provider or replay a second kernel. Model, formal lineage and Python runtime are shared. Their finite checks test instruments, closed instances and arithmetic; they cannot prove universal geometry or cost statements by sampling. An agreeing agent report is therefore not external mathematical validation.

Historical failed controls, wrong diagnostic/oracle cases, source exposures, bookkeeping corrections and the old malformed-memory failure remain in the project. The packet's verification-limits record distinguishes the selected final evidence from earlier exploratory history; the small packet is not a complete laboratory archive. The optional numeric candidate still contains explicit missing-body fault ports and has no full-solver certificate. Nothing here repairs those faults or transfers mathematical acceptance to that listing. Research and monitoring remain paused; this submission authorizes review of the supplied claim only.

## 12. Electronic appendices and review questions

`MANIFEST.json` and `CHECKSUMS.sha256` identify every included byte. `READING-MAP.md` translates historical appendix aliases and release names to the current portable files. `formal/CONTEXTS.json` gives exact separate module-provider contexts; similarly named sources are not flattened across contexts. `formal/SOURCE-MAP.json` binds portable source paths to original relative origins and hashes. `formal/BUILD-ORDER.json` provides each context's topological project import order. Compiled objects and local runtimes are omitted to keep the bundle small and to avoid presenting old cached objects as a fresh rebuild. No included file automatically starts a proof campaign.

The electronic appendix directories are: `algorithm/` for complete finite code/data/representation/projection; `mathematics/` for all detailed runtime, guard, graph, recipe, payload, generator, scalar, decoder and arithmetic arguments; `formal/` for full project proof sources; and `verification/` for the final reports, controls, contact limits and selected original audit receipts. Relative paths in this main document are portable; historical absolute locators inside immutable provenance copies are identities only and are not needed for reading.

An outside review should answer separately: (1) does the formal agreement/cut model coincide with ordinary rooted MAF; (2) do G0 and the actual Rule5 caller satisfy every original consumer premise; (3) does the actual-call construction cover every enabled body with correct multiplicity and physical order; (4) is the operational projection justified at every retained consumer; (5) do the five source channels and finite recipes pay every real operation, especially refused states and eager generators; (6) are the scalar/allocation invariants sufficient before applying width/fee bounds; and (7) does the explicit P/A composition leave any uncharged exponential work? A concrete failing branch, missing premise or arithmetic inequality is more useful than an overall confidence score.

No prior-art search or external bibliography is used to support novelty. The submission requests correctness review. Attribution and the relationship to existing algorithms require a separate literature assessment before publication or a best-known-bound claim.
