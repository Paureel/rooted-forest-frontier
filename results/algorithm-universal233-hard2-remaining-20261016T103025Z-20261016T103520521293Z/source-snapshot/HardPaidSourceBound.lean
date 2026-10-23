import Hard2OutputWeightedBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork CoreProgram SourceCoverage
open GenericForest.FrontierWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open Universal233.Rule5SelectedLocalWork Universal233.Hard2PaidLocal Universal233.Hard2Overlap

def hardPaidPolynomial (N Q : Nat) :=2*(hard2GenerationPolynomial N*(Q+1)+12*outputLocalPolynomial N)+6

theorem binary_prefix_absorb (K q : Nat) :
 ((K*2^(q+1)+6:Nat):Rat)≤((2*K+6:Nat):Rat)*Rule5ActualTrace.base^q := by
 have pow:=GenericForest.LocalPolynomial.two_power_le Rule5ActualTrace.base (by decide +kernel) q
 have product:=Rat.mul_le_mul_of_nonneg_left pow (show 0≤(2:Rat)*(K:Rat) from Rat.mul_nonneg (by decide) Rat.natCast_nonneg)
 have constant:=Rat.mul_le_mul_of_nonneg_left (call_base_pow_ge_one q) (show 0≤(6:Rat) by decide)
 have sum:=qadd_le_add product constant
 simpa only [Rat.natCast_add,Rat.natCast_mul,Rat.natCast_pow,Rat.natCast_ofNat,Rat.pow_succ,
  Rat.add_mul,Rat.mul_add,Rat.mul_assoc,Rat.mul_comm,Rat.mul_one,Rat.one_mul] using sum

/-- Complete literal hard-paid source bound, with its sharp output mass.
All local bodies are proved above. Ordinary callback work remains the exact
Nat query debit in hardPaidSource_split; no desired wholebody fee is assumed. -/
theorem hardPaidSource_bound (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (c : CherryBranching.Candidate) (out : Result) (q N Q : Nat)
 (three : 3≤N) (tn : treeNodes T≤N) (sn : treeNodes S≤N) (budget : q≤Q)
 (proper0 : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (selected : runHard2 T S c=some out) :
 ((hardPaidSource actual (fun _ _ _=>0) T S q c out).work:Rat)≤
 ((hardPaidPolynomial N Q:Rat)+geometric Rule5ActualTrace.base*forestCoefficient N Q*caseMass Rule5ActualTrace.base out)*Rule5ActualTrace.base^q := by
 have properParts:=(DepthOne.proper_iff T S).1 proper0
 have nt:=properParts.1
 have ns:=properParts.2.1
 have same:=properParts.2.2
 let os:=actualOutputs S T c q out
 have shape (o : Output) (mem:o∈os):=actual_output_shape S T c q out N ns sn o mem
 have gen:=actualOutputsMeter_bound T S c out N q three tn sn proper0 hard selected
 have exec:=fullOutputsSource_local actual (fun _ _ _=>0) T S q N os nt tn sn
  (by intro o mem;have s:=shape o mem;exact s.2)
 have count:=actual_output_count S T c q out
 have mul:=Nat.mul_le_mul_left (outputLocalPolynomial N) count
 have outer:=Nat.mul_le_mul_left (hard2GenerationPolynomial N) (show q+1≤Q+1 by omega)
 have outer2:=Nat.mul_le_mul_right (2^(q+1)) outer
 let K:=hard2GenerationPolynomial N*(Q+1)+12*outputLocalPolynomial N
 have natlocal:(hardPaidSource actual (fun _ _ _=>0) T S q c out).work≤K*2^(q+1)+6+
  outputForestDebit actual (fun _ _ _=>0) T S q os:=by
  simp only [hardPaidSource,actualOutputsMeter_value]
  dsimp only [K]
  dsimp only [os] at *
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm (outputLocalPolynomial N) 12] at *
  omega
 have debit:=outputForestDebit_weighted actual T S q N Q os (Nat.le_trans (leaves_nodes T) tn) budget
  (by intro o mem;exact OutputState.sourceForest_proper T S o.partition nt ns (fun x=>same.mem_iff) (shape o mem).1)
 have mass:=actual_paid_raw_mass proper0 hard selected q Rule5ActualTrace.base (by decide +kernel)
 have pos:0≤geometric Rule5ActualTrace.base*forestCoefficient N Q*Rule5ActualTrace.base^q:=
  Rat.mul_nonneg (Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg)
   (Rat.le_of_lt (Rat.pow_pos (by decide +kernel)))
 have weighted:=Rat.le_trans debit (Rat.mul_le_mul_of_nonneg_left mass pos)
 have localBill:=binary_prefix_absorb K q
 have total:=qadd_le_add localBill weighted
 have cast:=Rat.natCast_le_natCast.2 natlocal
 rw [Rat.natCast_add] at cast
 apply Rat.le_trans cast
 simpa only [hardPaidPolynomial,K,Rat.add_mul,Rat.mul_add,Rat.mul_assoc,Rat.mul_comm] using total
end OrdinaryDispatch.Hard2SourceWork
