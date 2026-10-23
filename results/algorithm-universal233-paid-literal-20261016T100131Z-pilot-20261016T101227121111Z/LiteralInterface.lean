import LiteralBinding
namespace Universal233.PaidLiteralDecisionWork
open RMAF Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork Rule5PaidSelector

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

end Universal233.PaidLiteralDecisionWork
