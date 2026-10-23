import PrefixScans
namespace Universal233.Rule5PrefixLocalWork
open RMAF

def leavesMeter : Tree→Measured (List Nat)
 | .leaf x=>⟨[x],1⟩
 | .node l r=>let a:=leavesMeter l;let b:=leavesMeter r
               ⟨a.value++b.value,a.work+b.work+a.value.length+2⟩

theorem leaves_value (T : Tree) : (leavesMeter T).value=leaves T := by
 induction T with
 | leaf x=>rfl
 | node l r hl hr=>simp only [leavesMeter,leaves,hl,hr]

theorem leaves_positive (T : Tree) : 1≤(leaves T).length := by
 induction T with
 | leaf x=>simp [leaves]
 | node l r hl hr=>simp only [leaves,List.length_append];omega

theorem quadratic_combine (a b wa wb : Nat) (ha : 1≤a) (hb : 1≤b)
 (hA : wa≤4*a*a) (hB : wb≤4*b*b) : wa+wb+a+2≤4*(a+b)*(a+b) := by
 have cross : a≤a*b := by have:=Nat.mul_le_mul_left a hb;simpa using this
 have pos : 1≤a*b := by have:=Nat.mul_le_mul ha hb;simpa using this
 simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
 rw [Nat.mul_comm b a]
 omega

theorem leaves_work (T : Tree) : (leavesMeter T).work≤4*(leaves T).length*(leaves T).length := by
 induction T with
 | leaf x=>simp [leavesMeter,leaves]
 | node l r hl hr=>
   have c:=quadratic_combine _ _ _ _ (leaves_positive l) (leaves_positive r) hl hr
   simpa only [leavesMeter,leaves_value,leaves,List.length_append] using c
end Universal233.Rule5PrefixLocalWork
