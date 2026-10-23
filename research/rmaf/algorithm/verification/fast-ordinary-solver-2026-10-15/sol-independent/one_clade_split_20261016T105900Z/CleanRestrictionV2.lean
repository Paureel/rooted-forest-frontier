/- Contacted prover: clade separation survives and reflects restriction. -/
import CleanClade
open RMAF ForestState Universal233 Universal233.HardParent
open IndependentGeometry IndependentOneExchange
namespace ContactedClade

def optionLeaves : Option Tree→List Nat
 | none=>[]
 | some T=>leaves T

theorem option_leaves_merge (l r : Option Tree) :
 optionLeaves (merge l r)=optionLeaves l++optionLeaves r := by
 cases l <;> cases r <;> simp [optionLeaves,merge,leaves]

theorem restrict_labels (T : Tree) (B : List Nat) (x : Nat) :
 x∈optionLeaves (restrict B T) ↔ x∈leaves T ∧ x∈B := by
 induction T with
 | leaf y => by_cases yb : y∈B <;> by_cases xy : x=y <;> simp [restrict,optionLeaves,leaves,yb,xy]
 | node l r il ir =>
  change x∈optionLeaves (merge (restrict B l) (restrict B r))↔_
  rw [option_leaves_merge,List.mem_append,il,ir]
  change (x∈leaves l ∧ x∈B) ∨ (x∈leaves r ∧ x∈B) ↔ (x∈leaves l++leaves r ∧ x∈B)
  rw [List.mem_append]
  constructor
  · rintro (⟨hl,hb⟩|⟨hr,hb⟩)
    · exact ⟨Or.inl hl,hb⟩
    · exact ⟨Or.inr hr,hb⟩
  · rintro ⟨h,hb⟩
    exact h.elim (fun hl=>Or.inl ⟨hl,hb⟩) (fun hr=>Or.inr ⟨hr,hb⟩)

theorem absent_restrict {T R : Tree} {B A : List Nat}
 (h : restrict B T=some R) (sub : ∀x∈A,x∈B) : Absent T A↔Absent R A := by
 have labels : ∀x,x∈leaves R↔x∈leaves T ∧ x∈B := by
  intro x;simpa only [h,optionLeaves] using restrict_labels T B x
 constructor
 · intro no x hx;exact no x ((labels x).1 hx).1
 · intro no x hx xa;exact no x ((labels x).2 ⟨hx,sub x xa⟩) xa

theorem absent_none {T : Tree} {B A : List Nat}
 (h : restrict B T=none) (sub : ∀x∈A,x∈B) : Absent T A := by
 intro x hx xa
 exact restrict_none_absent T B h x hx (sub x xa)

theorem clean_restrict (T : Tree) (B A D : List Nat)
 (subA : ∀x∈A,x∈B) (subD : ∀x∈D,x∈B) :
 ∀R,restrict B T=some R→(Clean A D T↔Clean A D R) := by
 induction T with
 | leaf x =>
  intro R h
  by_cases xb : x∈B
  · have eq : Tree.leaf x=R := by simpa [restrict,xb] using h
    subst R
    exact Iff.rfl
  · simp [restrict,xb] at h
 | node l r il ir =>
  intro R h
  cases hl : restrict B l with
  | none =>
   have al := absent_none hl subA
   have dl := absent_none hl subD
   cases hr : restrict B r with
   | none => simp [restrict,hl,hr] at h
   | some V =>
    have eq : V=R := by simpa only [restrict,hl,hr,Option.some.injEq] using h
    subst R
    rw [clean_node]
    constructor
    · intro cl
      apply (ir V hr).1
      rcases cl with ⟨ar,_⟩|⟨_,cr⟩|dnone
      · exact clean_absent_A r ar
      · exact cr
      · exact clean_absent_D r (fun x hx=>dnone x (List.mem_append_right _ hx))
    · intro cr
      exact Or.inr (Or.inl ⟨al,(ir V hr).2 cr⟩)
  | some L =>
   cases hr : restrict B r with
   | none =>
    have ar := absent_none hr subA
    have dr := absent_none hr subD
    have eq : L=R := by simpa only [restrict,hl,hr,Option.some.injEq] using h
    subst R
    rw [clean_node]
    constructor
    · intro cl
      apply (il L hl).1
      rcases cl with ⟨_,cl⟩|⟨al,_⟩|dnone
      · exact cl
      · exact clean_absent_A l al
      · exact clean_absent_D l (fun x hx=>dnone x (List.mem_append_left _ hx))
    · intro cl
      exact Or.inl ⟨ar,(il L hl).2 cl⟩
   | some V =>
    have eq : Tree.node L V=R := by simpa only [restrict,hl,hr,Option.some.injEq] using h
    subst R
    rw [clean_node,clean_node,absent_restrict hr subA,absent_restrict hl subA,il L hl,ir V hr,
     absent_restrict (T:=Tree.node l r) (R:=Tree.node L V) (by simp only [restrict,hl,hr]) subD]

theorem clean_agrees {T S : Tree} {B A D : List Nat}
 (same : restrictionAgrees T S B=true) (subA : ∀x∈A,x∈B) (subD : ∀x∈D,x∈B)
 (source : Clean A D S) : Clean A D T := by
 unfold restrictionAgrees at same
 cases ht : restrict B T with
 | none => simp only [ht] at same;contradiction
 | some L =>
  cases hs : restrict B S with
  | none => simp only [ht,hs] at same;contradiction
  | some R =>
   simp only [ht,hs] at same
   have sr := (clean_restrict S B A D subA subD R hs).1 source
   have tr := (iso_clean (same_iso same) A D).2 sr
   exact (clean_restrict T B A D subA subD L ht).2 tr
end ContactedClade
