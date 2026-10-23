# Preregistered source-operation accounting

This specification is independent of the unread work package. It defines a
finite reference source-operation ledger, not CPU instructions/cycles or a
certified compiler cost semantics. Exact vector comparisons here establish
instrument readiness only. Source-value agreement alone cannot establish work.

## Contacts and source locators

Main TARGET.md:5–13 requires total charged generation/search/reconstruction
cost and keeps all three milestones open. RMAF.lean:13–15 defines recursive
leaves with a left append. CoreProgram.lean:21–27 builds original origins and
colors and materializes groups; :29–46 normalizes and erases; :48–74 selects;
:91–106 appends receipts and attempts; :108–126 contains step/run/generate.
CoreGraph.lean's source supports and local singleton alternatives are proof
interfaces, not additional executable calls in generate. All four files and
prior reviewer/checker/audit knowledge are shared contacted inputs. No earlier
verifier or author/prover implementation is imported into this instrument.

The toolkit capability index has timing and receipt-integrity utilities but no
ordinary rooted-source operational cost ledger. Existing geometry/partition
checkers do not account for receipt materialization. A one-shot new ledger is
therefore warranted. No general toolkit registration or broad suite is needed.

## Required accounting sites

| Site | Required ledger demand |
|---|---|
| generate initialization | generate call; first leaves traversal and all its appends; Nodup check and list/equality demand; successful guard's second leaves traversal/length/subtraction/min; fromTree traversal, original-address left appends, one color-oracle call per original leaf |
| normalize | every visited grouped-tree node, color comparisons even when unequal, every successful homogeneous payload left append |
| groups / choose | tree traversal and left append of group lists; actual all/find short-circuit scans; filter scans, comparisons, kept-cell construction and filtered-list length; mixedCherry work and its final color comparison |
| erase / attempt | actual visited nodes and original-address equality calls; root/duplicate/entire refusal paths; cut membership demand; detached/cut cons; continued callback and counter update |
| run and pruning | each run/step; zero-budget still does normalize/choose/attempt/erase before the prune callback; do not charge zero because the callback has visited=0 |
| finish | detached payload map, another actual groups call, flatten/flatMap payload materialization, partition left append and emitted output cell |
| Receipt.combine / prefixRoot | both output and refusal left-list append lengths, even when result values agree; counter arithmetic and prefix counter update |

The reference evaluator uses an explicit eager source envelope for pure child
arguments (including both mixedCherry arguments to Option.or). Its exact
counts are reference-model counts. Library/compiler sharing or short-circuit
optimizations require their own relation to that envelope; no cycle equality
is asserted. Standard list combinators are represented with their input/output
traversal demand. A candidate using different primitive units may satisfy a
proved domination relation instead of equal numeric counters.

Append has a call charge and a separate left-cell demand. Empty-left append
has zero copied cells but still a call. Receipt joins can have exponentially
many left output records at one prefix; a bound on prefix count alone does
not bound each materialized join by the current tree size. A total-work
argument must account globally for all left output/refusal list lengths.

## Units, assumptions and encoded input

The event vector is structural. Tree-node visits, primitive calls, list-cell
demands, payload copying and number/address comparisons have separately named
units, with no arbitrary sum described as machine time. Node visits include
constant constructor/control overhead under the stated source model.

An arbitrary color function is an oracle. Record its call count and, where a
literal supplied tariff C is used, the separate C-times-calls quantity. No
uniform runtime bound for the oracle is inferred from its return values.
Label/color equality, Nat arithmetic and address equality retain argument-size
metadata; their machine/bit cost needs explicit library/encoding assumptions.
Input label/color widths and an oversized budget's bit width do not disappear
when min clips recursive depth to n−1. Counter additions also involve encoded
integers. The finite ledger does not prove bounds on those widths or cycles.
Bit lengths are parameters/obligations, not measured bit-operation counts or
automatic lower bounds. Parsing, instrumentation and report generation are
observer costs; their measured pilot time is not the source program's runtime.

The direct Nodup reference scan is a declared simple list implementation; its
comparison count is not a certification of Lean Std's chosen implementation.
The required initial check/list-size demand is independent of that choice.

## Plants and validation

Literal inputs, expected value fields and selected structural counts are fixed
in CONTROL-PIN.json before execution. Full events/counters remain in receipts;
the finite assertions do not claim exhaustive operation-proof coverage.
Validate contiguous unique event IDs, exported totals against their records,
literal value/count fields and explicit encoding/oracle metadata.

Run each corrupt report beside its clean original. Corruptions preserve the
returned value while removing left-append demand, zeroing work before pruning,
omitting initial Nodup/color charges, or omitting/duplicating records. Both
internally inconsistent corruptions and internally retotalled omissions must
be rejected. This tests the work comparison separately from value projection.

Before candidate acceptance, source-bind every work definition and its unit
contract, prove or scope its relation to the unchanged CoreProgram expression,
trace initialization/attempts/prunes/refusals and receipt materialization, and
separate source-operation bounds from oracle/bit/machine claims. All three
main milestones remain open regardless of a local work theorem.
