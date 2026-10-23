/- Contacted prover: restriction agreement is hereditary to nonempty subblocks. -/
import OneExchangeOpenStatements
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange
namespace ContactedClade

def restrictOption (A : List Nat) (o : Option Tree) := o.bind (restrict A)

theorem restrict_merge (A : List Nat) (l r : Option Tree) :
 restrictOption A (merge l r)=merge (restrictOption A l) (restrictOption A r) := by
 have mn : ∀t,merge t none=t := by intro t;cases t <;> rfl
 have nm : ∀t,merge none t=t := by intro t;cases t <;> rfl
 cases l <;> cases r <;> simp only [merge,restrictOption,Option.bind_none,Option.bind_some,restrict]
 all_goals first | rfl | exact (mn _).symm | exact (nm _).symm

theorem filter_contains (A B : List Nat) (x : Nat) :
 (B.filter A.contains).contains x=B.contains x && A.contains x := by
 apply Bool.eq_iff_iff.2
 simp only [List.contains_iff_mem,List.mem_filter,Bool.and_eq_true,List.contains_iff_mem]

theorem restrict_filter (A B : List Nat) (T : Tree) :
 restrict (B.filter A.contains) T=restrictOption A (restrict B T) := by
 induction T with
 | leaf x => cases ha : A.contains x <;> cases hb : B.contains x <;>
    simp [restrict,filter_contains,ha,hb,restrictOption]
 | node l r il ir =>
  change merge (restrict (B.filter A.contains) l) (restrict (B.filter A.contains) r)=_
  rw [il,ir,←restrict_merge]
  rfl

theorem restrict_ext (T : Tree) (A B : List Nat) (eq : ∀x,A.contains x=B.contains x) :
 restrict A T=restrict B T := by
 induction T with
 | leaf x => simp only [restrict,eq x]
 | node l r il ir =>
  change merge (restrict A l) (restrict A r)=merge (restrict B l) (restrict B r)
  rw [il,ir]

theorem restrict_subset (T : Tree) {A B : List Nat} (sub : ∀x∈A,x∈B) :
 restrictOption A (restrict B T)=restrict A T := by
 rw [←restrict_filter]
 apply restrict_ext
 intro x
 apply Bool.eq_iff_iff.2
 simp only [List.contains_iff_mem,List.mem_filter,List.contains_iff_mem]
 exact ⟨fun h=>h.2,fun h=>⟨sub x h,h⟩⟩

theorem restrict_iso {T U : Tree} (iso : RootedIso T U) (A : List Nat) :
 MaybeIso (restrict A T) (restrict A U) := by
 induction iso with
 | leaf x => cases h : A.contains x <;> simp only [restrict,h] <;>
    first | exact .none | exact .some (.leaf x)
 | straight hl hr il ir => exact merge_iso il ir
 | swapped hl hr il ir => exact merge_iso_swap il ir

theorem restriction_agrees_subset {T S : Tree} {A B : List Nat}
 (old : restrictionAgrees T S B=true) (sub : ∀x∈A,x∈B)
 (hit : ∃x,x∈A ∧ x∈leaves T) : restrictionAgrees T S A=true := by
 have rel : MaybeIso (restrictOption A (restrict B T)) (restrictOption A (restrict B S)) := by
  unfold restrictionAgrees at old
  cases ht : restrict B T <;> cases hs : restrict B S <;> simp only [ht,hs] at old
  all_goals first | contradiction | exact restrict_iso (same_iso old) A
 rw [restrict_subset T sub,restrict_subset S sub] at rel
 apply nonnull_iso_agrees rel
 intro no
 obtain ⟨x,xa,xt⟩ := hit
 exact restrict_none_absent T A no x xt xa

theorem split_shapes {T S : Tree} {F : List (List Nat)}
 (hF : agreement T S F=true) (X : List Nat) :
 (splitForest X F).all (restrictionAgrees T S)=true := by
 have checks := hF
 simp only [agreement,Bool.and_eq_true] at checks
 have part := checks.1.1.1.1
 have shapes := checks.1.1.2
 have labels : ∀B∈F,∀x∈B,x∈leaves T := by
  simp only [partitionCheck,Bool.and_eq_true] at part
  intro B bF x xB
  exact List.contains_iff_mem.1 (List.all_eq_true.1 part.2 x (List.mem_flatten.2 ⟨B,bF,xB⟩))
 apply List.all_eq_true.2
 intro A aSplit
 obtain ⟨B,bF,aParts⟩ := List.mem_flatMap.1 aSplit
 have nonempty : A≠[] := by
  intro empty
  have yes := (List.mem_filter.1 aParts).2
  simp [empty] at yes
 have sub : ∀x∈A,x∈B := by
  have choices := (List.mem_filter.1 aParts).1
  simp only [List.mem_cons,List.mem_singleton] at choices
  rcases choices with rfl|rfl <;> exact fun x hx=>(List.mem_filter.1 hx).1
 apply restriction_agrees_subset (List.all_eq_true.1 shapes B bF) sub
 cases A with
 | nil => exact False.elim (nonempty rfl)
 | cons x xs => exact ⟨x,by simp,labels B bF x (sub x (by simp))⟩
end ContactedClade
