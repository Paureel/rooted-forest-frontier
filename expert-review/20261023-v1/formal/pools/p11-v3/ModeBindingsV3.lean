import Rule4ConsumerV3
namespace SourceForestV3
open RMAF SourceCouplingV2 SourceDisjointV2
theorem cutoff_spec (parent : Nat) (base : Tree→Tree→Nat→Option SourceForestV3.F) :
    ordinarySpec (.cutoff parent) base=
      OrdinaryDispatch.FastOrdinary.cutoff (fun b T S=>base T S b) parent := by
  funext T S b
  simp only [ordinarySpec,enabled,OrdinaryDispatch.FastOrdinary.cutoff,decide_eq_true_eq]
end SourceForestV3
