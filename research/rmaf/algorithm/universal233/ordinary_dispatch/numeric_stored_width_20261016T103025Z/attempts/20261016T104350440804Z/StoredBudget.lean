import StoredPolicy
import BinaryProducerAccounting
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer

theorem disjoint_budget_width (B W N : Nat) (t : GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits)
 (tc : TreeWidth W t) (sc : SourcesWidth W ss) (qb : q.length≤B) (count : ss.length≤2*N)
 (js : List (Job (GenericForest.BinaryProvider.Tree×GenericForest.BinaryProvider.Tree) GenericForest.BinaryProvider.Forest))
 (built : (jobsBits t ss).value=some js) :
 (allocationBits q (knownBits js).value (pendingBits js).value).value.length≤B+4*N+3 := by
 have local:=disjoint_allocated_width W t ss q tc sc js built
 omega

theorem disjoint_run_call_width (B W N : Nat)
 (solve : (GenericForest.BinaryProvider.Tree×GenericForest.BinaryProvider.Tree)→Bits→Charged (Option (Bits×GenericForest.BinaryProvider.Forest)))
 (t : GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits)
 (tc : TreeWidth W t) (sc : SourcesWidth W ss) (qb : q.length≤B) (count : ss.length≤2*N)
 (js : List (Job (GenericForest.BinaryProvider.Tree×GenericForest.BinaryProvider.Tree) GenericForest.BinaryProvider.Forest))
 (built : (jobsBits t ss).value=some js) (c : Bits)
 (mem : c∈(runBits solve (allocationBits q (knownBits js).value (pendingBits js).value).value js).value.calls) : c.length≤B+4*N+3 := by
 have eq:=(runBits_storage solve _ js).2.2.2 c mem
 rw [eq]
 exact disjoint_budget_width B W N t ss q tc sc qb count js built

/-- Available budget operations only. The complete represented recursion must
still bind this relation to the actual ordinary/forest source trace. -/
inductive BudgetPath (N : Nat) (q0 : Bits) : Nat→Bits→Prop where
 | root : BudgetPath N q0 0 q0
 | pay {d q} (cuts : List RMAF.Vertex) : BudgetPath N q0 d q→cuts.length≤2*N→
   BudgetPath N q0 (d+1) (subtractBits q (spineCounter cuts).value).value
 | allocated {d q W t ss js} : BudgetPath N q0 d q→TreeWidth W t→SourcesWidth W ss→
   (jobsBits t ss).value=some js→ss.length≤2*N→
   BudgetPath N q0 (d+1) (allocationBits q (knownBits js).value (pendingBits js).value).value

theorem budget_path_width (Bq N : Nat) (q0 : Bits) (initial : q0.length≤Bq)
 {d q} (path : BudgetPath N q0 d q) : q.length≤Bq+(4*N+3)*d := by
 induction path with
 | root=>simpa using initial
 | @pay d q cuts path count ih=>
  have counter:=spineCounter_length cuts
  have width:=subtractBits_length q (spineCounter cuts).value
  simp only [Nat.mul_add,Nat.mul_one]
  omega
 | @allocated d q W t ss js path tc sc built count ih=>
  have bound:=disjoint_budget_width (Bq+(4*N+3)*d) W N t ss q tc sc ih count js built
  simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using bound

def budgetStorageWidth (Bq N Q : Nat) : Nat := Bq+(4*N+3)*(Q+N)

theorem global_budget_width (Bq N Q : Nat) (q0 : Bits) (initial : q0.length≤Bq)
 {d q} (path : BudgetPath N q0 d q) (depth : d≤Q+N) : q.length≤budgetStorageWidth Bq N Q := by
 have bound:=budget_path_width Bq N q0 initial path
 have scaled:=Nat.mul_le_mul_left (4*N+3) depth
 unfold budgetStorageWidth
 omega

/-- Both input storage widths remain explicit. L is the independent semantic
label-bit parameter in the previous numeric package, and is not substituted. -/
def scalarStorageWidth (B Bq N Q : Nat) : Nat := max (markerStorageWidth B N Q) (budgetStorageWidth Bq N Q)
end OrdinaryDispatch.StoredNumeric
