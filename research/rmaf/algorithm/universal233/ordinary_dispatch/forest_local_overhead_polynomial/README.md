# Concrete polynomial forest-only source bill

Import Monomial. Namespace GenericForest.LocalPolynomial.

monomial_local_overhead derives the frozen LocalOverheadBound with zero
ordinaryWork and the concrete coefficient

    K = 2^50 * (N+Q+2)^8,

for rational c>=2 and current target label count <=N. The resulting bound on
every proper current state's printed nonrecursiveBill is K*c^q for q<=Q.
No ordinary semantic or work IH is used to prove that local bill inequality.

source_work_monomial_size_capped takes the separate finite
SizeCappedOrdinaryBillBound W N Q c D and, for c>2, proves

    sourceWork ordinary W T ss q
      <= (D + K/(1-2/c))*c^q.

The supplied ordinary coefficient D is paid once. The size-capped premise
covers only proper query pairs with both leaf counts<=N and budget<=Q; the
completed frontier support theorem supplies those caps.

The proof retains every term of the literal frozen zero-work bill:

- proper source/tree volume, original cut-address cells and output label cells;
- CoreWork.generate_work_bound, including failed/pruned prefixes and every
  literal source occurrence, plus actual meterColorLabel scans for every leaf;
- all ordered source-pair minimal-span and address membership charges;
- all raw outputs (count <=12*2^q), actual replacement states, full forest
  materialization and repeated inspections/minimum comparisons;
- literal scheduler caller work; its ordinary recursive charge is zero here.

The intermediate overheadPolynomial is explicit and has a proved monomial
envelope <=2^50*M^8 for M>=2. The constant and exponent are deliberately loose.
They support a concrete recurrence coefficient, not a timing estimate.

This is a bound on the frozen source-accounting functions. The declared
inspectionBill/primitive source-operation convention and unbounded scalar
bit/payload correspondence remain qualified. In particular this does not
prove machine/runtime-IR correspondence or that the printed inspection sheet
already covers every actual returned callback payload. The parent owns that
source/bill review and the complete dispatcher recurrence. All main milestones,
independent acceptance and novelty remain OPEN; c=2.33 remains conditional,
q=k_opt-1 and no implicit rho.
