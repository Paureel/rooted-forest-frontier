import HullMono
namespace FreshClade
open RMAF
def combine : Option Tree → Option Tree → Option Tree
 | none,none => none
 | some a,none => some a
 | none,some b => some b
 | some a,some b => some (.node a b)
theorem restrict_node (C : List Nat) (l r : Tree) :
 restrict C (.node l r)=combine (restrict C l) (restrict C r) := rfl
theorem bind_combine (C : List Nat) (a b : Option Tree) :
 (combine a b).bind (restrict C)=combine (a.bind (restrict C)) (b.bind (restrict C)) := by
 cases a with
 | none =>
   cases b with
   | none => rfl
   | some b => cases he : restrict C b <;> simp [combine,he]
 | some a =>
   cases b with
   | none => cases he : restrict C a <;> simp [combine,he]
   | some b => rfl
theorem restrict_subset (B C : List Nat) (h : ∀x,x∈C→x∈B) (T : Tree) :
 (restrict B T).bind (restrict C)=restrict C T := by
 induction T with
 | leaf x =>
   by_cases hb : x∈B
   · simp [restrict,hb]
   · have hc : x∉C := fun hx => hb (h x hx)
     simp [restrict,hb,hc]
 | node l r il ir => rw [restrict_node,bind_combine,il,ir,restrict_node]

inductive OptIso : Option Tree → Option Tree → Prop
 | none : OptIso none none
 | some {T S : Tree} : RootedIso T S → OptIso (some T) (some S)
theorem combine_iso {a b c d : Option Tree} (h : OptIso a c) (k : OptIso b d) :
 OptIso (combine a b) (combine c d) := by
 cases h <;> cases k
 · exact .none
 · exact .some (by assumption)
 · exact .some (by assumption)
 · exact .some (.straight (by assumption) (by assumption))
theorem combine_swap_iso {a b c d : Option Tree} (h : OptIso a d) (k : OptIso b c) :
 OptIso (combine a b) (combine c d) := by
 cases h <;> cases k
 · exact .none
 · exact .some (by assumption)
 · exact .some (by assumption)
 · exact .some (.swapped (by assumption) (by assumption))
theorem restrict_iso (C : List Nat) {T S : Tree} (h : RootedIso T S) :
 OptIso (restrict C T) (restrict C S) := by
 induction h with
 | leaf x => by_cases hx : x∈C <;> simp [restrict,hx]; exact .some (.leaf x); exact .none
 | straight h₁ h₂ i₁ i₂ => exact combine_iso i₁ i₂
 | swapped h₁ h₂ i₁ i₂ => exact combine_swap_iso i₁ i₂

theorem restrict_selected (C : List Nat) (T : Tree) {x : Nat} (hc : x∈C) (ht : x∈leaves T) :
 restrict C T≠none := by
 induction T with
 | leaf y => simp [leaves] at ht; subst y; simp [restrict,hc]
 | node l r il ir =>
   simp only [leaves,List.mem_append] at ht
   rcases ht with ht|ht
   · have hn := il ht
     cases hl : restrict C l <;> cases hr : restrict C r <;> simp_all [restrict]
   · have hn := ir ht
     cases hl : restrict C l <;> cases hr : restrict C r <;> simp_all [restrict]

theorem restriction_refine (B C : List Nat) {T S : Tree}
 (h : ∀x,x∈C→x∈B) (ne : C≠[]) (labels : ∀x,x∈C→x∈leaves T)
 (a : restrictionAgrees T S B=true) : restrictionAgrees T S C=true := by
 have nt : restrict C T≠none := by
  cases C with
  | nil => contradiction
  | cons x C => exact restrict_selected (x::C) T (by simp) (labels x (by simp))
 have oi : OptIso (restrict C T) (restrict C S) := by
  unfold restrictionAgrees at a
  cases ht : restrict B T with
  | none => simp [ht] at a
  | some t =>
    cases hs : restrict B S with
    | none => simp [ht,hs] at a
    | some s =>
      simp only [ht,hs] at a
      have oo := restrict_iso C (sameShape_iso a)
      have et := restrict_subset B C h T
      have es := restrict_subset B C h S
      simp only [ht,Option.bind_some] at et
      simp only [hs,Option.bind_some] at es
      rw [et,es] at oo
      exact oo
 generalize ht : restrict C T=t at oi
 generalize hs : restrict C S=s at oi
 cases oi with
 | none => exact False.elim (nt ht)
 | some hi =>
   unfold restrictionAgrees
   rw [ht,hs]
   exact iso_sameShape hi
end FreshClade
