import PaidBuilderOuter
namespace Universal233.Rule5RemainingLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard

theorem one_calls_count (T : Tree) (v : RMAF.Vertex) (R : BottomData) : (oneCalls T v R).length≤1 := by
 unfold oneCalls;split <;> simp

theorem build_one_ledger (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) (R : BottomData) :
 (buildOneMeter fee T S a b d u v R).work≤oneBudget (leaves T).length v.length 0+
 ((oneCalls T v R).map fee).sum := by
 have st:=subtree_work T v;have aa:=leaf_address_work T R.a;have ab:=leaf_address_work T R.b
 unfold oneBudget
 simp only [buildOneMeter,bump_work]
 split
 · rename_i C qa ub hc ha hb
   have eq : oneCalls T v R=[⟨R,C,qa,ub⟩]:=by simp [oneCalls,hc,ha,hb]
   rw [eq]
   simp only [bump_work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
   split <;> dsimp only <;> omega
 · dsimp only
   omega

/-- Ordered literal guard calls made before the first successful row. -/
def findCalls {α β γ : Type} (f : α→Measured (Option β)) (g : α→List γ) : List α→List γ
 | []=>[]
 | x::xs=>g x++match (f x).value with | some _=>[] | none=>findCalls f g xs

theorem find_calls_domain {α β γ : Type} (f : α→Measured (Option β)) (g : α→List γ)
 (xs : List α) {j : γ} (mem : j∈findCalls f g xs) : ∃x,x∈xs ∧ j∈g x := by
 induction xs with
 | nil=>simp [findCalls] at mem
 | cons x xs ih=>
  simp only [findCalls,List.mem_append] at mem
  rcases mem with hj|hj
  · exact ⟨x,by simp,hj⟩
  · split at hj
    · simp at hj
    · obtain ⟨y,hy,hj⟩:=ih hj
      exact ⟨y,by simp [hy],hj⟩

theorem find_calls_count {α β γ : Type} (f : α→Measured (Option β)) (g : α→List γ)
 (xs : List α) (point : ∀x,x∈xs→(g x).length≤1) : (findCalls f g xs).length≤xs.length := by
 induction xs with
 | nil=>simp [findCalls]
 | cons x xs ih=>
  have a:=point x (by simp);have r:=ih (fun y hy=>point y (by simp [hy]))
  simp only [findCalls,List.length_append,List.length_cons]
  split <;> simp only [List.length_nil] <;> omega

theorem find_builder_ledger {α β γ : Type} (f : α→Measured (Option β)) (g : α→List γ)
 (fee : γ→Nat) (xs : List α) (A : Nat)
 (cost : ∀x,x∈xs→(f x).work≤A+((g x).map fee).sum) :
 (findBuilderMeter f xs).work≤(A+2)*xs.length+1+((findCalls f g xs).map fee).sum := by
 induction xs with
 | nil=>simp [findBuilderMeter,findCalls]
 | cons x xs ih=>
  have a:=cost x (by simp);have r:=ih (fun y hy=>cost y (by simp [hy]))
  simp only [findBuilderMeter,findCalls,List.map_append,List.sum_append,List.length_cons,Nat.mul_succ]
  split <;> simp only [List.map_nil,List.sum_nil,Nat.add_zero] <;> dsimp only <;> omega

def secondCalls (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) : List LiteralCall :=
 findCalls (buildOneMeter fee T S a b d u v) (oneCalls T v) (rowsMeter S a b d.c).value

theorem second_calls_domain (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) {j : LiteralCall} (mem : j∈secondCalls fee T S a b d u v) :
 LiteralCallDomain T S a b d v j := by
 obtain ⟨R,hr,hj⟩:=find_calls_domain _ _ _ mem
 exact one_calls_domain T S a b d v R (by rw [←rows_value];exact hr) hj

theorem second_calls_count (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) : (secondCalls fee T S a b d u v).length≤32*(leaves S).length := by
 have h:=find_calls_count (buildOneMeter fee T S a b d u v) (oneCalls T v) (rowsMeter S a b d.c).value
  (fun R _=>one_calls_count T v R)
 exact h.trans (rows_count S a b d.c)

theorem second_builder_ledger (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
 (u v : RMAF.Vertex) :
 (secondBuilderMeter fee T S a b d u v).work≤secondBuilderBudget (leaves T).length (leaves S).length v.length 0+
 ((secondCalls fee T S a b d u v).map fee).sum := by
 have rs:=rows_work S a b d.c;have count:=rows_count S a b d.c
 have f:=find_builder_ledger (buildOneMeter fee T S a b d u v) (oneCalls T v) fee (rowsMeter S a b d.c).value
  (oneBudget (leaves T).length v.length 0) (fun R _=>build_one_ledger fee T S a b d u v R)
 have scale:=Nat.mul_le_mul_left (oneBudget (leaves T).length v.length 0+2) count
 simp only [secondBuilderMeter,secondBuilderBudget,secondCalls] at *
 omega
end Universal233.Rule5RemainingLocalWork
