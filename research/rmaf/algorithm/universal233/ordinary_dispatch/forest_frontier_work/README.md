# Forest ordinary frontier and separate overhead

Import OverheadBound. Namespace GenericForest.FrontierWork.

frontier follows the frozen solve/sourceWork guards and all literal overlap
branch occurrences. A completed or malformed state contributes no external
ordinary query. A singleton contributes its exact target/source/q query. A
disjoint state retains meterSchedule's exact queried pairs and budgets,
including the failing query. An overlap contributes every paid child frontier,
with no deduplication. This is a source-level accounting trace; no identity to
compiler instructions, runtime IR or machine traces is asserted.

frontier_queries_proper proves every retained ordinary pair proper and its
budget <= q. queryEnvelope_le_one proves the scheduler envelope <= 1 even for
a sole hard job. branch_mass_sharp retains the actual two raw generator lists
and proves mass <= 2/c. frontier_mass_bound consequently proves normalized
ordinary-query mass <= 1 for every proper source state and rational c >= 2.
No semantic ordinary IH is used in these mass statements.

source_work_split is an exact identity for ALL inputs:

    sourceWork ordinary W T ss q
      = sourceWork ordinary zeroWork T ss q
        + sum_{(t,s,b) in frontier} (W t s b).

The two public coefficient premises are separate:

- LocalOverheadBound bounds the frozen printed nonrecursiveBill with zero
  ordinaryWork by K*c^b on every proper current state with b <= Q.
- OrdinaryBillBound bounds W t s b by D*c^b only on proper ordinary pairs and
  budgets b <= Q.

For rational c > 2 and nonnegative K,D, source_work_bound_separated proves

    sourceWork ordinary W T ss q
      <= (D + geometric(c)*K)*c^q,
    geometric(c) = 1/(1-2/c),

for proper states and q <= Q. The ordinary callback coefficient D is paid once;
forest_overhead_bound charges only the zero-ordinary-work summand. The factor
is finite only under the printed strict c > 2 premise.

The local overhead premise is still an obligation, not a proved polynomial
coefficient. Existing source-operation/scalar charging conventions and primitive
source/bill correspondence remain qualified. The parent owns the complete
ordinary dispatcher and source/bit/payload recurrence. All main milestones,
independent acceptance and novelty remain OPEN. c=2.33 remains conditional,
q=k_opt-1, no implicit rho.
