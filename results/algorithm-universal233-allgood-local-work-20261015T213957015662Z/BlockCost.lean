import SolveCost
namespace AllGoodDP.LocalWork
open RMAF Universal233.WholeSourceWork Universal233.CoreWork

theorem delta_le_one (a b : Nat) : delta a b≤1 := by unfold delta;split <;> omega

theorem changes_nodes (p : Paint) : changes p+1≤paintNodes p := by
 induction p with
 | leaf => simp [changes,paintNodes]
 | node c l r il ir =>
  have a := delta_le_one c (root l)
  have b := delta_le_one c (root r)
  simp only [changes,paintNodes]
  omega

theorem split_cells (p : Paint) :
 (split p).1.length+(split p).2.flatten.length=(leaves (erase p)).length := by
 induction p with
 | leaf => rfl
 | node c l r il ir =>
  cases hl:c==root l <;> cases hr:c==root r <;>
   simp [split,hl,hr,erase,leaves,List.length_append] at * <;> omega

theorem split_payload (p : Paint) : (split p).1.length≤paintNodes p ∧ (split p).2.length+1≤paintNodes p := by
 have cells := split_cells p
 have lab := leaves_le_nodes (erase p)
 have changes := changes_nodes p
 rw [←paintNodes_erase] at lab
 rw [split_length]
 omega

/-- The four literal equality tests and both left append spines are charged.
The forest blocks retain empty components until the production final filter. -/
def meterSplit : Paint→Charged (List Nat×List (List Nat))
 | .leaf x _ => ⟨([x],[]),8⟩
 | .node c l r =>
  let a := meterSplit l
  let b := meterSplit r
  let la := if c==root l then a.value.1 else []
  let lb := if c==root r then b.value.1 else []
  let fa := if c==root l then a.value.2 else a.value.1::a.value.2
  let fb := if c==root r then b.value.2 else b.value.1::b.value.2
  ⟨(la++lb,fa++fb),a.work+b.work+4*(la.length+fa.length+2)+16⟩
@[simp] theorem meterSplit_value (p : Paint) : (meterSplit p).value=split p := by
 induction p with
 | leaf => rfl
 | node c l r il ir => simp [meterSplit,split,il,ir]

theorem meterSplit_work (p : Paint) (N : Nat) (hp : paintNodes p≤N) :
 (meterSplit p).work≤32*(N+1)*paintNodes p := by
 induction p with
 | leaf => simp [meterSplit,paintNodes];omega
 | node c l r il ir =>
  have hl : paintNodes l≤N := by simp only [paintNodes] at hp;omega
  have hr : paintNodes r≤N := by simp only [paintNodes] at hp;omega
  have a := il hl
  have b := ir hr
  have caps := split_payload l
  have loc : 4*((if c==root l then (split l).1 else []).length+
   (if c==root l then (split l).2 else (split l).1::(split l).2).length+2)+16≤32*(N+1) := by
   cases h:c==root l <;> simp only [h,Bool.false_eq_true,if_false,if_true,List.length_nil,List.length_cons] <;> omega
  simp only [Nat.mul_add,Nat.mul_one] at a b loc
  simp only [meterSplit,meterSplit_value,paintNodes,Nat.mul_add,Nat.mul_one]
  omega

def meterNonempty : List (List Nat)→Charged (List (List Nat))
 | [] => ⟨[],4⟩
 | B::F =>
  let m := meterNonempty F
  ⟨if B.isEmpty then m.value else B::m.value,m.work+8⟩
@[simp] theorem meterNonempty_value (F : List (List Nat)) :
 (meterNonempty F).value=F.filter (fun b=>!b.isEmpty) := by
 induction F with
 | nil => rfl
 | cons B F ih => cases B <;> simp [meterNonempty,ih]
theorem meterNonempty_work (F : List (List Nat)) : (meterNonempty F).work=8*F.length+4 := by
 induction F with
 | nil => rfl
 | cons B F ih => simp only [meterNonempty,List.length_cons,Nat.mul_add,Nat.mul_one];omega

def meterBlocks (p : Paint) : Charged (List (List Nat)) :=
 let m := meterSplit p
 let n := meterNonempty (m.value.1::m.value.2)
 ⟨n.value,m.work+n.work+8⟩
@[simp] theorem meterBlocks_value (p : Paint) : (meterBlocks p).value=blocks p := by simp [meterBlocks,blocks,rawBlocks]

def blocksBill (N : Nat) := 32*(N+1)*N+8*N+12

theorem meterBlocks_work (p : Paint) (N : Nat) (hp : paintNodes p≤N) :
 (meterBlocks p).work≤blocksBill N := by
 have s := meterSplit_work p N hp
 have size := (split_payload p).2
 have mul := Nat.mul_le_mul_left (32*(N+1)) hp
 simp only [meterBlocks,meterNonempty_work,meterSplit_value,List.length_cons,blocksBill]
 omega
end AllGoodDP.LocalWork
