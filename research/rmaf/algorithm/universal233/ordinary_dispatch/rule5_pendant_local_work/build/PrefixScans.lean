import Rule5Defs
namespace Universal233.Rule5PrefixLocalWork
open RMAF
structure Measured (α : Type) where
 value : α
 work : Nat
 deriving Repr

/-- Exactly the List.elem/contains early-stop value, with one scalar equality
and list/branch visit charged per nonempty cell. Scalar bit fee stays explicit. -/
def containsMeter (x : Nat) : List Nat→Measured Bool
 | []=>⟨false,1⟩
 | y::ys=>if x==y then ⟨true,2⟩ else
          let r:=containsMeter x ys;⟨r.value,r.work+2⟩

theorem contains_value (x : Nat) (ys : List Nat) : (containsMeter x ys).value=ys.contains x := by
 induction ys with
 | nil=>rfl
 | cons y ys ih=>
   simp only [containsMeter,List.contains_cons]
   split <;> simp_all

theorem contains_work (x : Nat) (ys : List Nat) : (containsMeter x ys).work≤2*ys.length+1 := by
 induction ys with
 | nil=>simp [containsMeter]
 | cons y ys ih=>simp only [containsMeter];split <;> simp only [List.length_cons] <;> omega

theorem missing_contains_work (x : Nat) (ys : List Nat) (miss : x∉ys) :
 (containsMeter x ys).work=2*ys.length+1 := by
 induction ys with
 | nil=>rfl
 | cons y ys ih=>
   have ne : (x==y)=false := by simp only [beq_eq_false_iff_ne];intro e;subst x;exact miss (by simp)
   have tail:=ih (fun hy=>miss (by simp [hy]))
   simp only [containsMeter,ne,Bool.false_eq_true,ite_false,tail,List.length_cons]
   omega

/-- Mirrors actual nodupDecidable/instDecidablePairwise: the TAIL decision
comes first, then the universal head-inequality scan only on a nodup tail. -/
def nodupMeter : List Nat→Measured Bool
 | []=>⟨true,1⟩
 | x::xs=>let r:=nodupMeter xs
          if r.value then let c:=containsMeter x xs;⟨!c.value,r.work+c.work+1⟩
          else ⟨false,r.work+1⟩

theorem nodup_value (xs : List Nat) : (nodupMeter xs).value=decide xs.Nodup := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>
   apply Bool.eq_iff_iff.2
   simp only [nodupMeter,ih]
   split
   · simp only [Bool.not_eq_true',contains_value,Bool.eq_false_iff,List.contains_iff_mem,List.nodup_cons]
     simp_all
   · simp_all

theorem nodup_work (xs : List Nat) : (nodupMeter xs).work≤2*(xs.length+1)*(xs.length+1) := by
 induction xs with
 | nil=>simp [nodupMeter]
 | cons x xs ih=>
   have c:=contains_work x xs
   simp only [nodupMeter]
   split <;> simp only [List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at * <;> omega

/-- Literal all-members guard, retaining the early false stop and all failed
membership visits inside that occurrence. -/
def allContainsMeter (B : List Nat) : List Nat→Measured Bool
 | []=>⟨true,1⟩
 | x::xs=>let c:=containsMeter x B
          if c.value then let r:=allContainsMeter B xs;⟨r.value,c.work+r.work+1⟩
          else ⟨false,c.work+1⟩

theorem all_contains_value (A B : List Nat) :
 (allContainsMeter B A).value=A.all B.contains := by
 induction A with
 | nil=>rfl
 | cons x A ih=>simp only [allContainsMeter,List.all_cons,contains_value];split <;> simp_all

theorem all_contains_work (A B : List Nat) :
 (allContainsMeter B A).work≤(2*B.length+2)*A.length+1 := by
 induction A with
 | nil=>simp [allContainsMeter]
 | cons x A ih=>
   have c:=contains_work x B
   simp only [allContainsMeter]
   split <;> simp only [List.length_cons,Nat.mul_succ] <;> omega
end Universal233.Rule5PrefixLocalWork
