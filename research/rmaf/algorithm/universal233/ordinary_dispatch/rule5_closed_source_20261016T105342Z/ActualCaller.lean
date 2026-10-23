import SourcePolynomial
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryCommonSplit.Source
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion OrdinaryDispatch.FastOrdinary
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence GenericForest.FrontierWork
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork

def rule5AnswerSource (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) : Charged (Option Forest) :=
 let r:=source cb W T S a b q
 ⟨match r.value with | .answered answer=>answer | _=>none,r.work+2⟩

theorem rule5_answer_value (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :
 (rule5AnswerSource cb W T S a b q).value=OrdinaryDispatch.Hard2Dispatcher.rule5Answer cb T S a b q := by
 simp only [rule5AnswerSource,source_value,OrdinaryDispatch.Hard2Dispatcher.rule5Answer]
 cases Rule5OrdinaryDispatch.dispatch cb T S a b q <;> rfl

theorem rule5_answer_split (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :
 (rule5AnswerSource cb W T S a b q).work=(rule5AnswerSource cb (fun _ _ _=>0) T S a b q).work+
 queryWork W (calls cb W T S a b q) := by
 have h:=source_split cb W T S a b q;simp only [rule5AnswerSource];omega

def actualCallback (q : Nat) : Ordinary :=cutoff OrdinaryDispatch.FastOrdinary.solve q

def actualRule5Source (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :=rule5AnswerSource (actualCallback q) W T S a b q

theorem admitted_proper {T S : Tree} {a b : Nat} (ad:admitted T S a b=true) : DepthOne.proper T S=true := by
 have p:=properPair_parts (admitted_parts ad).1
 exact (DepthOne.proper_iff T S).2 ⟨p.1,p.2.1,(List.perm_ext_iff_of_nodup p.1 p.2.1).2 p.2.2⟩

/-- The source invocation's original input/budget/label domain. Neither q nor
Q is bounded by any reduced leaf count. These are source-input conditions. -/
structure InputDomain (T S : Tree) (q N Q L : Nat) : Prop where
 size : (leaves T).length≤N
 budget : q≤Q
 targetLabels : ∀x,x∈leaves T→x<2^L
 sourceLabels : ∀x,x∈leaves S→x<2^L

theorem actual_rule5_bound {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true) (q N Q L : Nat) (domain:InputDomain T S q N Q L) :
 ((actualRule5Source (fun _ _ _=>0) T S a b q).work:Rat)≤(C5 N Q L:Rat)*Rule5ActualTrace.base^q := by
 have hp:=admitted_proper ad
 have eq:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have targetCap:=domain.size
 have sourceCap:(leaves S).length≤N:=by omega

 have pow:=call_base_pow_ge_one q
 have positive:0≤Rule5ActualTrace.base^q:=Rat.le_trans (by decide +kernel) pow
 -- The two wrapper inspections use the explicit spare constant in C5.
 -- First obtain the tighter source bound before the coefficient's spare 4.
 obtain ⟨z,sel0,_⟩:=final_classification_complete ch ad
 have sel:(finalMeter checkFee T S a b).value=some z:=by rw [final_value];exact sel0
 have local0:=dispatch_concrete_local (actualCallback q) (cutoff_sound q) ch ad hp q L sel domain.targetLabels domain.sourceLabels
 have cap:=selected_prefix_cap T S domain.size sourceCap z
 have localNat:(source (actualCallback q) (fun _ _ _=>0) T S a b q).work+2≤prefixCap N+selectedForestDebit (actualCallback q) checkFee (literalFee T S a b) T S a b q z+2:=by omega
 have lr:=Rat.natCast_le_natCast.2 localNat
 simp only [Rat.natCast_add,Rat.natCast_ofNat] at lr
 have forests:=selected_forest_debit_bound (actualCallback q) ch ad q N Q sel domain.size sourceCap domain.budget
 have debit:=Rat.le_trans forests (forest_envelope_coefficient N Q L q)
 have prefScaled:=Rat.mul_le_mul_of_nonneg_left pow (Rat.natCast_nonneg (a:=prefixCap N+2))
 rw [Rat.mul_one,Rat.natCast_add,Rat.natCast_ofNat] at prefScaled
 have total:=Rat.le_trans (Rat.add_le_add_right.mpr prefScaled) (Rat.add_le_add_left.mpr debit)
 have c0:(prefixCap N:Rat)+2+(80*(2^50*(N+Q+L+2)^8):Nat)≤(C5 N Q L:Rat):=by
  unfold C5;simp only [Rat.natCast_add,Rat.natCast_ofNat]
  have h:(0:Rat)≤2:=by decide +kernel
  have step:((prefixCap N:Rat)+(80*(2^50*(N+Q+L+2)^8):Nat))+2≤((prefixCap N:Rat)+(80*(2^50*(N+Q+L+2)^8):Nat))+4:=
   Rat.add_le_add_left.mpr (by decide +kernel : (2:Rat)≤4)
  simpa only [Rat.add_assoc,Rat.add_comm,Rat.add_left_comm] using step
 have scaled:=Rat.mul_le_mul_of_nonneg_right c0 positive
 change (((source (actualCallback q) (fun _ _ _=>0) T S a b q).work+2:Nat):Rat)≤_
 rw [Rat.natCast_add,Rat.natCast_ofNat]
 apply Rat.le_trans lr
 apply Rat.le_trans (b:=((prefixCap N:Rat)+2+(80*(2^50*(N+Q+L+2)^8):Nat))*Rule5ActualTrace.base^q) ?_ scaled
 have total':(prefixCap N:Rat)+2+selectedForestDebit (actualCallback q) checkFee (literalFee T S a b) T S a b q z≤
  ((prefixCap N:Rat)+2+(80*(2^50*(N+Q+L+2)^8):Nat))*Rule5ActualTrace.base^q:=by
  apply Rat.le_trans (Rat.add_le_add_left.mpr debit)
  simpa only [Rat.add_mul] using Rat.add_le_add_right.mpr prefScaled
 simpa only [actualRule5Source,rule5AnswerSource,Rat.add_assoc,Rat.add_comm,Rat.add_left_comm] using total'
end Universal233.Rule5ClosedSource
