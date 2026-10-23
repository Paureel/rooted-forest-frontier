import LiteralBinding
namespace Universal233.PaidLiteralDecisionWork
open RMAF Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork Rule5PaidSelector
open Rule5FinalClassification

/-- Canonical bounded request evaluator. The fee is its computed inspection bill. -/
def evaluateCall (T S : Tree) (a b : Nat) (j : LiteralCall) : Measured Bool :=
 literalMeter T S a b j.selection j.u j.v j.row j.core j.qa j.ub

theorem evaluate_call_value (T S : Tree) (a b : Nat) (j : LiteralCall) :
 (evaluateCall T S a b j).value=decide
  (LiteralProps T S a b j.selection j.u j.v j.row j.core j.qa j.ub) :=
 literal_value T S a b j.selection j.u j.v j.row j.core j.qa j.ub

theorem evaluate_call_work (T S : Tree) (a b : Nat) (j : LiteralCall) :
 (evaluateCall T S a b j).work=literalFee T S a b j := rfl

theorem paid_selected_value_concrete (classFee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (paidSelectedMeter classFee (literalFee T S a b) T S a b).value=buildSelected T S a b :=
 paid_selected_value classFee (literalFee T S a b) T S a b

theorem paid_selected_ledger_concrete (classFee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (paidSelectedMeter classFee (literalFee T S a b) T S a b).work≤(finalMeter classFee T S a b).work+
 secondBuilderBudget (leaves T).length (leaves S).length (leaves T).length 0+3+
 ((paidSelectedCalls classFee (literalFee T S a b) T S a b).map (literalFee T S a b)).sum :=
 paid_selected_ledger classFee (literalFee T S a b) T S a b

/-- Every compared external taxon label is bounded on an actual paid call.
The unused singletonArc field is not inspected by LiteralProps. -/
theorem literal_call_scalar_bits (classFee : CheckRequest→Nat) (T S : Tree) (a b L : Nat)
 (d : BadSelection) (u v : RMAF.Vertex)
 (sel : (finalMeter classFee T S a b).value=some (.remaining d (.second u v)))
 (j : LiteralCall) (dom : LiteralCallDomain T S a b d u v j)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L) :
 a<2^L ∧ b<2^L ∧ d.c<2^L ∧ j.row.a<2^L ∧ j.row.b<2^L ∧
 (∀x,x∈leaves j.row.X→x<2^L) ∧ (∀x,x∈leaves j.core→x<2^L) := by
 have p:=literal_call_bits T S a b d u v dom L tlabs slabs
 have row:=row_payload S a b d.c dom.1
 have select:=final_payload classFee T S a b sel
 have cb:=slabs d.c select.2.2.1
 have ab : a<2^L ∧ b<2^L := by
  rcases row.2.2.2 with ⟨ha,hb⟩|⟨ha,hb⟩
  · rw [←ha,←hb];exact ⟨p.2.2.1,p.2.2.2⟩
  · rw [←hb,←ha];exact ⟨p.2.2.2,p.2.2.1⟩
 exact ⟨ab.1,ab.2,cb,p.2.2.1,p.2.2.2,p.1,p.2.1⟩

end Universal233.PaidLiteralDecisionWork
