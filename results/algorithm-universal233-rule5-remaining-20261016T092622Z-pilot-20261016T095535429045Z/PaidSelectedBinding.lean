import PaidBuilderLedger
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard

/-- buildSelected literally calls selectFinal again. The caller's previous
selection does not replace this second executed classifier occurrence. -/
def paidSelectedMeter (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b : Nat) : Measured (Option (SelectedPaid T S)) :=
 let cls:=finalMeter classFee T S a b
 match cls.value with
 | some (.remaining d (.second u v))=>
   let r:=secondBuilderMeter literalFee T S a b d u v
   ⟨r.value.map (SelectedPaid.mk d u v),cls.work+r.work+2⟩
 | _=>⟨none,cls.work+1⟩

theorem paid_selected_value (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b : Nat) :
 (paidSelectedMeter classFee literalFee T S a b).value=buildSelected T S a b := by
 simp only [paidSelectedMeter,final_value,buildSelected]
 cases h:selectFinal T S a b with
 | none=>rfl
 | some z=>cases z with
   | «prefix» s=>rfl
   | remaining d z=>cases z <;> simp only [second_builder_value]

def paidSelectedBudget (nt ns Kc Kl : Nat) :=finalBudget nt ns Kc+secondBuilderBudget nt ns nt Kl+3

theorem second_budget_mono (nt ns m M K : Nat) (h : m≤M) :
 secondBuilderBudget nt ns m K≤secondBuilderBudget nt ns M K := by
 unfold secondBuilderBudget oneBudget
 have scaled:=Nat.mul_le_mul_right (32*ns) (show 2*m+2*leafAddressBudget nt+K+8+2≤2*M+2*leafAddressBudget nt+K+8+2 by omega)
 omega

theorem paid_selected_work (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b L Kc Kl : Nat)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L)
 (classifier : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r→classFee r≤Kc)
 (literal : ∀d u v,(finalMeter classFee T S a b).value=some (.remaining d (.second u v))→
  ∀j,LiteralCallDomain T S a b d u v j→literalFee j≤Kl) :
 (paidSelectedMeter classFee literalFee T S a b).work≤paidSelectedBudget (leaves T).length (leaves S).length Kc Kl := by
 have cls:=final_work classFee T S a b L Kc tlabs slabs classifier
 simp only [paidSelectedMeter]
 split
 · rename_i d u v sel
   have payload:=final_payload classFee T S a b sel
   have vn : v.length≤(leaves T).length:=payload.2.2.2.2
   have builder:=second_builder_work literalFee T S a b d u v Kl (literal d u v sel)
   have mono:=second_budget_mono (leaves T).length (leaves S).length v.length (leaves T).length Kl vn
   unfold paidSelectedBudget
   dsimp only;omega
 · unfold paidSelectedBudget
   dsimp only;omega

def paidSelectedCalls (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b : Nat) : List LiteralCall :=
 match (finalMeter classFee T S a b).value with
 | some (.remaining d (.second u v))=>secondCalls literalFee T S a b d u v
 | _=>[]

theorem paid_selected_calls_count (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b : Nat) : (paidSelectedCalls classFee literalFee T S a b).length≤32*(leaves S).length := by
 unfold paidSelectedCalls
 split
 · exact second_calls_count _ _ _ _ _ _ _ _
 · simp

theorem paid_selected_calls_domain (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b : Nat) {j : LiteralCall} (mem : j∈paidSelectedCalls classFee literalFee T S a b) :
 ∃d u v,(finalMeter classFee T S a b).value=some (.remaining d (.second u v)) ∧
 LiteralCallDomain T S a b d u v j ∧ u.length≤(leaves T).length ∧ v.length≤(leaves T).length ∧
 d.badArc.length+1≤(leaves S).length ∧ d.c∈leaves S := by
 unfold paidSelectedCalls at mem
 split at mem
 · rename_i d u v sel
   have p:=final_payload classFee T S a b sel
   exact ⟨d,u,v,sel,second_calls_domain _ _ _ _ _ _ _ _ mem,p.2.2.2.1,p.2.2.2.2,p.1,p.2.2.1⟩
 · simp at mem
/-- Unconditional outer source bill with the exact ordered unresolved guard
fee ledger. This does not assert those guard fees have polynomial cost. -/
theorem paid_selected_ledger (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
 (T S : Tree) (a b : Nat) :
 (paidSelectedMeter classFee literalFee T S a b).work≤(finalMeter classFee T S a b).work+
 secondBuilderBudget (leaves T).length (leaves S).length (leaves T).length 0+3+
 ((paidSelectedCalls classFee literalFee T S a b).map literalFee).sum := by
 simp only [paidSelectedMeter]
 split
 · rename_i d u v sel
   have p:=final_payload classFee T S a b sel
   have builder:=second_builder_ledger literalFee T S a b d u v
   have mono:=second_budget_mono (leaves T).length (leaves S).length v.length (leaves T).length 0 p.2.2.2.2
   have calls : paidSelectedCalls classFee literalFee T S a b=secondCalls literalFee T S a b d u v := by
    simp only [paidSelectedCalls,sel]
   rw [calls]
   dsimp only;omega
 · dsimp only;omega

end Universal233.Rule5RemainingLocalWork
