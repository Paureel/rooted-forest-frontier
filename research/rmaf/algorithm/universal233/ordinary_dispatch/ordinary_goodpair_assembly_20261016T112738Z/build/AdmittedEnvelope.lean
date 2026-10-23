import AdmittedWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

theorem and_sequence_call_count (fs : List (Unit→CheckReceipt Bool)) :
 (andSequence fs).calls.length≤(fs.map (fun f=>(f ()).calls.length)).sum := by
 induction fs with
 | nil=>simp [andSequence]
 | cons f fs ih=>
   simp only [andSequence]
   split <;> (try dsimp only) <;> simp only [List.length_append,List.map_cons,List.sum_cons] <;> omega

theorem admitted_call_count (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (admittedMeter fee T S a b).calls.length≤2+(partitionMeter S a b).value.length := by
 have c:=and_sequence_call_count (admittedGuards fee T S a b (partitionMeter S a b).value)
 simp only [admittedMeter,admittedGuards,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
   liftMeter,checkMeter,filteredLengthMeter,restriction_filter_calls,List.length_nil,List.length_cons,
   List.length_map,Nat.zero_add,Nat.add_zero,Nat.add_assoc] at c ⊢
 omega

theorem admitted_call_count_polynomial (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) :
 (admittedMeter fee T S a b).calls.length≤2*(leaves S).length+3 := by
 have c:=admitted_call_count fee T S a b
 have p:=partition_domain S a b
 omega

/-- Complete nonrecursive source bill for the literal admitted predicate,
including its strict P let. The only primitive boundary is the named checker
fee on a proved bounded domain, plus separately stated scalar/cell bit fee. -/
theorem admitted_scaled_work (scalarFee : Nat) (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 scalarFee*(admittedMeter fee T S a b).work≤
 scalarFee*admittedBudget (leaves T).length (leaves S).length K :=
 Nat.mul_le_mul_left scalarFee (admitted_work fee T S a b L K tlabs slabs primitive)
end Universal233.Rule5PendantLocalWork
