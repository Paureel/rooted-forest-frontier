import Work
import Branches

/-! Actual selected groups and stored detached payloads, using frozen chooser
selection lemmas. No cut-component theorem is imported or assumed. -/
namespace Universal233.CoreWork
open RMAF CoreProgram Integration

def Selected (t : GTree) (g : Group) : Prop :=
  choose t = .one g ∨ (∃ h, choose t = .two g h ∨ choose t = .two h g)

theorem selected_mem (t g) (h : Selected t g) : g ∈ groups t := by
  rcases h with h | ⟨b,h | h⟩
  · exact (choose_one_selected t g h).1
  · obtain ⟨p,hp,_⟩ := choose_two_selected t g b h
    exact groupLeaf_mem_groups t _ g (gcherry_left hp)
  · obtain ⟨p,hp,_⟩ := choose_two_selected t b g h
    exact groupLeaf_mem_groups t _ g (gcherry_right hp)

def groupVolume (g : Group) : Nat := 1+g.labels.length+g.origin.length

def detachedVolume : List Group → Nat
  | [] => 0
  | g::d => groupVolume g + detachedVolume d

/-- Every actual successful attempted child, including an overbudget child
before its constant pruned continuation, has this literal guard/erase shape. -/
inductive Prefix (start : GTree) : Nat → GTree → List Group → List Vertex → Prop
  | initial : Prefix start 0 start [] []
  | next {depth t d c g u} : Prefix start depth t d c →
      Selected (normalize t) g → g.origin ≠ [] → c.contains g.origin ≠ true →
      erase g.origin (normalize t) = some u →
      Prefix start (depth+1) u (g::d) (g.origin::c)

theorem prefix_sizes (start depth t d c) (h : Prefix start depth t d c) :
    footprint t ≤ footprint start ∧ d.length = depth ∧ c.length = depth ∧
    detachedVolume d ≤ depth*footprint start ∧
    (∀ g ∈ d, groupVolume g ≤ footprint start) ∧
    (∀ v ∈ c, v.length ≤ footprint start) := by
  induction h with
  | initial => simp [detachedVolume]
  | @next depth t d c g u hp hs hr hn he ih =>
    have hf := normalize_footprint t
    have he' := erase_footprint g.origin (normalize t) u he
    have hg := group_size (normalize t) g (selected_mem _ _ hs)
    change groupVolume g ≤ footprint (normalize t) at hg
    have hgs : groupVolume g ≤ footprint start := Nat.le_trans hg (Nat.le_trans hf ih.1)
    refine ⟨Nat.le_trans he' (Nat.le_trans hf ih.1),?_,?_,?_,?_,?_⟩
    · simpa only [List.length_cons] using congrArg (·+1) ih.2.1
    · simpa only [List.length_cons] using congrArg (·+1) ih.2.2.1
    · simp only [detachedVolume,Nat.add_mul,Nat.one_mul]
      omega
    · intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · simpa only [ha] using hgs
      · exact ih.2.2.2.2.1 a ha
    · intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        unfold groupVolume at hgs
        omega
      · exact ih.2.2.2.2.2 v hv

/-- Polynomial stored-state bounds also cover the final pruned attempted child.
The depth condition is B for evaluated prefixes, B+1 for attempted children. -/
theorem capped_prefix_sizes (start depth t d c B)
    (h : Prefix start depth t d c) (hd : depth ≤ B+1) :
    footprint t ≤ footprint start ∧ d.length ≤ B+1 ∧ c.length ≤ B+1 ∧
    detachedVolume d ≤ (B+1)*footprint start := by
  obtain ⟨hf,hdlen,hclen,hvol,_,_⟩ := prefix_sizes start depth t d c h
  refine ⟨hf,by omega,by omega,?_⟩
  exact Nat.le_trans hvol (Nat.mul_le_mul_right _ hd)

end Universal233.CoreWork
