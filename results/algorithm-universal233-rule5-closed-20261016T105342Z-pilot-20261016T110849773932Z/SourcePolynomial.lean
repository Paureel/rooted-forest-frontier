import ForestDebitBounds
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion OrdinaryDispatch.WorkIntegration
open WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork

/-- Explicit source coefficient. prefixCap is a positive Nat polynomial
spelled out through source-cap definitions in UniformPrefix. L is retained
as the actual input-width parameter; no binary cost interpretation is made. -/
def C5 (N Q L : Nat) : Nat :=prefixCap N+80*(2^50*(N+Q+L+2)^8)+4

theorem forest_envelope_coefficient (N Q L q : Nat) :
 5*forestEnvelope N Q q≤(80*(2^50*(N+Q+L+2)^8):Nat)*Rule5ActualTrace.base^q := by
 have geom:5*geometric Rule5ActualTrace.base≤(80:Rat):=by decide +kernel
 have coeff:forestCoefficient N Q≤((2^50*(N+Q+L+2)^8:Nat):Rat):=by
  unfold forestCoefficient
  apply Rat.natCast_le_natCast.2
  exact Nat.mul_le_mul_left (2^50) (Nat.pow_le_pow_left (by omega) 8)
 have p0:0≤forestCoefficient N Q:=by unfold forestCoefficient;exact Rat.natCast_nonneg
 have pp:=Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q)
 have c0:0≤(80:Rat):=by decide +kernel
 have gscale:=Rat.mul_le_mul_of_nonneg_right geom p0
 have cscale:=Rat.mul_le_mul_of_nonneg_left coeff c0
 have scale:=Rat.mul_le_mul_of_nonneg_right (Rat.le_trans gscale cscale) pp
 simpa only [forestEnvelope,Rat.natCast_mul,Rat.natCast_ofNat,Rat.mul_assoc] using scale

theorem source_bound (cb : Ordinary) (sound:CallbackSound cb)
 {T S : Tree} {i : RMAF.Vertex} {a b : Nat} (ch:CherryAt T i a b) (ad:admitted T S a b=true)
 (hp:DepthOne.proper T S=true) (q N Q L : Nat)
 (tn:(leaves T).length≤N) (sn:(leaves S).length≤N) (budget:q≤Q)
 (tlabs:∀x,x∈leaves T→x<2^L) (slabs:∀x,x∈leaves S→x<2^L) :
 ((source cb (fun _ _ _=>0) T S a b q).work:Rat)≤(C5 N Q L:Rat)*Rule5ActualTrace.base^q := by
 obtain ⟨z,sel0,_⟩:=final_classification_complete ch ad
 have sel:(finalMeter checkFee T S a b).value=some z:=by rw [final_value];exact sel0
 have local0:=dispatch_concrete_local cb sound ch ad hp q L sel tlabs slabs
 have cap:=selected_prefix_cap T S tn sn z
 have localNat:(source cb (fun _ _ _=>0) T S a b q).work≤prefixCap N+selectedForestDebit cb checkFee (literalFee T S a b) T S a b q z:=by omega
 have localRat:=Rat.natCast_le_natCast.2 localNat
 rw [Rat.natCast_add] at localRat
 have forest:=selected_forest_debit_bound cb ch ad q N Q sel tn sn budget
 have coefficient:=forest_envelope_coefficient N Q L q
 have debit:=Rat.le_trans forest coefficient
 have pow:=call_base_pow_ge_one q
 have prefix:=Rat.mul_le_mul_of_nonneg_left pow (Rat.natCast_nonneg (a:=prefixCap N))
 rw [Rat.mul_one] at prefix
 have total:=Rat.add_le_add prefix debit
 have c0:(prefixCap N:Rat)+(80*(2^50*(N+Q+L+2)^8):Nat)≤(C5 N Q L:Rat):=by
  unfold C5;simp only [Rat.natCast_add];exact Rat.le_add_right Rat.natCast_nonneg
 have scale:=Rat.mul_le_mul_of_nonneg_right c0 (Rat.le_trans (by decide +kernel : (0:Rat)≤1) pow)
 apply Rat.le_trans localRat
 apply Rat.le_trans total
 simpa only [Rat.add_mul] using scale
end Universal233.Rule5ClosedSource
