import LiteralStructural
namespace Universal233.PaidLiteralDecisionWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork
open Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard Case322Extraction

def notMeter (m : Measured Bool) : Measured Bool := ⟨!m.value,m.work+1⟩
def orMeter (m : Measured Bool) (f : Unit→Measured Bool) : Measured Bool :=
 if m.value then ⟨true,m.work+1⟩ else let n:=f ();⟨n.value,m.work+n.work+1⟩

theorem or_value (m : Measured Bool) (f : Unit→Measured Bool) :
 (orMeter m f).value=(m.value || (f ()).value) := by
 simp only [orMeter];split <;> simp_all

theorem or_work (m : Measured Bool) (f : Unit→Measured Bool) :
 (orMeter m f).work≤m.work+(f ()).work+1 := by
 simp only [orMeter];split <;> dsimp only <;> omega

def cutsTwoMeter (S : Tree) (a b : Nat) : Measured Bool :=
 let c:=cutsMeter S a b;⟨decide (c.value.length=2),c.work+c.value.length+3⟩

theorem cuts_two_value (S : Tree) (a b : Nat) :
 (cutsTwoMeter S a b).value=decide ((CherryBranching.cuts S a b).length=2) := by
 simp only [cutsTwoMeter,cuts_value]

def literalChecks (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) : List (Unit→Measured Bool) :=
 [fun _=>properPairMeter T S,
  fun _=>bump 10 (atTreeMeter S R.w (bottom R.sa R.sc R.sb R.a R.b d.c R.X)),
  fun _=>cherryExistsMeter T R.a R.b,
  fun _=>cutsTwoMeter S R.a R.b,
  fun _=>labelsMeter T C R.X d.c,
  fun _=>containsTreeMeter C R.b,
  fun _=>notMeter (containsTreeMeter C d.c),
  fun _=>leafAtMeter T qa R.a,
  fun _=>leafAtMeter T ub R.b,
  fun _=>leafAtMeter T u d.c,
  fun _=>orMeter (incidentEqMeter T R.X u v) (fun _=>incidentEqMeter T R.X v u),
  fun _=>tailMemMeter T R.X v,
  fun _=>tailMemMeter T R.X u,
  fun _=>notMeter (minimalMemMeter T R.X v),
  fun _=>notMeter (minimalMemMeter T R.X u),
  fun _=>boundaryEqMeter S R.X d.badArc,
  fun _=>⟨decide (EndpointOrder a b R.a R.b),9⟩]

/-- Actual finite, computable guard decision, in the frozen conjunction order.
The primitive structural subroutines are reused without a fee assumption. -/
def literalMeter (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) : Measured Bool :=
 checksMeter (literalChecks T S a b d u v R C qa ub)

theorem literal_value (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) :
 (literalMeter T S a b d u v R C qa ub).value=decide (LiteralProps T S a b d u v R C qa ub) := by
 apply Bool.eq_iff_iff.2
 simp only [literalMeter,checks_value,literalChecks,List.all_cons,List.all_nil,
  proper_pair_value,bump_value,at_tree_value,cherry_exists_value,cuts_two_value,labels_value,
  contains_tree_value,leaf_at_value,or_value,incident_eq_value,tail_mem_value,minimal_mem_value,
  boundary_eq_value,notMeter,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',Bool.and_true,
  decide_eq_true_eq,Bool.eq_false_iff,List.contains_iff_mem]
 simp [LiteralProps,and_assoc]

/-- Concrete executable fee; fixed invocation inputs stay outside LiteralCall. -/
def literalFee (T S : Tree) (a b : Nat) (j : LiteralCall) : Nat :=
 (literalMeter T S a b j.selection j.u j.v j.row j.core j.qa j.ub).work

end Universal233.PaidLiteralDecisionWork
