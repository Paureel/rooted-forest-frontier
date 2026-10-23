# Determinism of the constructed graph data

This is an additive supporting proof for the mathematical implementation. It
supplies the identification needed when a correspondence interface returns an
existential ledger. An existential witness is not, merely by its existence,
the ledger constructed from the actual evaluation. The statement and proof
below are part of the proposed author argument to be checked.

Fix a relation `R(T,S,b,a)` that is functional in `a`:

```
R(T,S,b,a) and R(T,S,b,a') imply a = a'.
```

Fix every computational input of a graph family, including its mode, initial
index, input lists, choices and route tag. Then any two derivations in that
family have equal computational result data and equal output lists of slots,
debits, cells and occurrences. This is equality of the displayed data, not
uniqueness of proof terms. All logical fields retain their full types; proof
irrelevance identifies their values when the same computational choice is used.
No totality assumption on R is needed to compare two existing derivations.

For the application here, the parent's ordinary induction hypothesis supplies
`R(T,S,b,a) -> a = base(T,S,b)`. This implies the required functionality even
when two distinct actual child invocations have the same arguments and return.
Those invocations still have distinct enclosing list/slot positions. Functional
return values do not identify occurrences or authorize deduplication.

## Primitive invocation and scheduler data

For `Invoke`, the fixed enabled Boolean separates `refused` from `returned`.
The refused data are its fixed None/slot expression. In the enabled case, R's
functionality fixes the child answer; the displayed slot and index are then
fixed. `PairChild` applies its fixed option map, so it preserves uniqueness.

Induct on the fixed job list for the coupling `Run` graph. Nil has its unique
constant receipt. A resolved head has its one fixed resolved result and its
unique tail. At a hard head, enabledness first selects refused or entered.
For an entered head the unique callback answer separates None from Some.
The failed constructor has no executed tail; the successful constructor has
the unique tail at its specified next index. Calls, visits, ticks and slots
are computed by the constructor's fixed arithmetic/list expressions. Hence
all output data are equal. The fixed affordability test and this result prove
`Schedule`/`ScheduleAt` uniqueness. This argument keeps duplicate equal jobs
as distinct list cells.

## Forest and children data

Prove `ForestExec` and `BranchesExec` data uniqueness by strong induction on the
forest budget, with a subordinate induction on the fixed branch list. The
actual properness/agreement, target option, source-list shape, overlap option
and scheduler-job option tests separate the outer constructors. Each terminal
case has one displayed result expression. Singleton/disjoint scheduler cases
use the primitive uniqueness just proved.

On an eligible overlap branch, the constructor premises include
`1 <= cutCount` and `cutCount <= budget`. The recursive forest budget is
therefore strictly smaller. The induction hypothesis fixes that branch's
result and slots. Its tail starts at the fixed index
`k + length(out.slots)` and is unique by list induction. An ineligible branch
has only its skip constructor. These are the only recursive forest cases, so
the induction proves all forest/branch output data unique for every fixed
mode and input. It uses no reduced-leaf budget cap and no successful-answer
premise.

Next induct on the fixed children list. Affordability separates refusal from
execution. An executed head has the unique forest result, debit and slots;
the structural tail is unique whether that forest returned None or Some.
The constructor's answer, call, check and debit expressions are then fixed.
This proves `ChildrenExec` uniqueness without dropping failed children.
COMMON's strict leaf comparison likewise selects its one constructor, whose
entered answer is fixed by R.

## Remaining constructor families

The remaining graph families nest the preceding graphs without a new cyclic
dependency. Their list folds use structural induction. The following case
inventory identifies each discriminator and the data fixed in its cases.

| Family | Discriminator and unique subdata |
|---|---|
| Rule4 `AnswersExec` and full-output `OutputsExec` | The fixed input tail at `i+1` is unique first. Head affordability selects refusal or the unique forest result; the displayed head cell, including a failed answer's Some(result), is fixed. |
| Good pair | The initial-budget test, fixed DP option and score comparison are disjoint. The returned case uses the unique residual forest result. Prepare/score/finish are fixed functions. |
| Maf callback | The fixed pair of restriction options separates missing from returned. Returned uses the unique forest data; missing has its fixed None and empty lists. |
| Retained and literal/group schedulers | Their now unique adapter answer fixes failed versus succeeded and whether a tail exists. Job-list induction fixes all remaining receipts, tags and query lists. |
| BothBad dispatch and entries | The fixed Entry.mode separates the dispatch cases. Each dispatch uses unique forest/adapter subdata; entries list induction fixes head, tail and offsets. |
| Group evaluation/output/pair | The fixed output/subtree/check selections determine the unique local case. The nested literal scheduler is unique; evaluation-list induction fixes all concatenations and retained views. |
| Rule5 setup/selected/common/current/request | The fixed setup/pretest/outside/selector/builder options and comparisons separate their cases. Existing forest/children/invocation uniqueness fixes each nested execution. Common jobs and answer/request lists use structural induction at their displayed offsets. |
| Disjoint/unit/paid wrappers | The fixed input singleton/partition/route data select their subgraphs. Those subgraphs are unique, and the result and label functions are fixed; the paid-before-unit chronology and unit-before-paid recording remain different fixed lists. |

For every row, comparing two derivations begins with the same fixed tests and
tagged inputs, so different incompatible constructors cannot occur. In the
matching constructor, the indicated smaller graph/list induction fixes each
subresult; substitution into its pure constructor expression fixes the whole
result. No correspondence theorem, ledger existence theorem, desired source
projection or assumed runtime count is used for this uniqueness argument.

Finally the distinct `Hard2Route` tags separate the enclosing RouteExec and
RouteLedger constructors. A refused or direct tag fixes empty occurrence
lists and its explicit result. A disjoint or admitted tag has the unique
subexecution and fixed linear labelling. A paid tag has the unique paid/unit
subexecution and its two fixed labelled lists. Thus, for fixed
`R,T,S,c,q,route`,

```
RouteLedger R T S c q route pr  rec  chrono
RouteLedger R T S c q route pr' rec' chrono'
    imply pr = pr' and rec = rec' and chrono = chrono'.
```

Here `pr` is the route result before the enclosing `finish T S c q` wrapper;
it is not silently identified with that wrapper's complete charged result.

## Applying the existential source interface

The actual-subevaluation induction constructs the actual route graph,
`Hard2Exec` and a RouteLedger with its particular `pr,rec,chrono`. Its route
is the fixed value of `hard2FrontMeter T S c q`. The sound R hypothesis is
already available from the ordinary induction; it does not assume the parent.

Apply the full `hard2_trace_ledger` interface to that constructed Hard2Exec
and the actual secondary candidate `d`. It supplies some `pr',rec',chrono'`
with a RouteLedger at exactly the same fixed route, together with the
canonical return equality, permutation, pairwise label inequality, query
projection and SlotRealizes facts. The uniqueness result identifies all three
existential fields with the actual constructed fields. Substitution therefore
transfers those facts to the actual chronological attempt word. It does not
choose the existential witness as a purported runtime evaluation.

The existing labelled-position interfaces now apply to that particular ledger.
Pairwise unequal labels preserve duplicate equal query values. Their local
injection, prefixed by the parent source address, gives the global actual-body
injection used by the query-count induction. Refused or unused SOURCE positions
may remain outside its image. Their local executed comparisons and returns
stay in the operation count.

This lemma adds no new runtime field, callback, evaluation, erasure, code body,
fee or input premise. It is a mathematical constructor induction, not a new
whole-runtime formal certificate. Its role is only to discharge the
existential-ledger identification in the full dynamic adequacy proof.
