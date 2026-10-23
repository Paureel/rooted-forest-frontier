import SourceWork
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration HardParent CherryBranching Rule5Local

inductive LocalSelection where
 | large (e : RMAF.Vertex)
 | two (c : SizeTwoSelection)
 | outside (c : OutsideSelection)
 | remaining
 deriving Repr, DecidableEq

/-- Exact source priority for the proved prefix. The remaining constructor
retains the unproved Case3.2 classification obligation explicitly. -/
def selectLocal (T S : Tree) (a b : Nat) : Option LocalSelection :=
 if admitted T S a b then
   match selectLarge T S a b with
   | some e => some (.large e)
   | none => match selectSizeTwo T S a b with
     | some c => some (.two c)
     | none => match selectOutside T S a b with
       | some c => some (.outside c)
       | none => some .remaining
 else none

def localChildren (S : Tree) (a b : Nat) : LocalSelection → List Child
 | .large _ => [pendantChild S a b]
 | .two c => fiveChildren S a b c.p c.q
 | .outside c => fiveChildren S a b c.p c.q
 | .remaining => []

theorem selectLocal_cases {T S : Tree} {a b : Nat} {s : LocalSelection}
 (h : selectLocal T S a b = some s) : admitted T S a b = true ∧
 match s with
 | .large e => selectLarge T S a b = some e
 | .two c => selectLarge T S a b = none ∧ selectSizeTwo T S a b = some c
 | .outside c => selectLarge T S a b = none ∧ selectSizeTwo T S a b = none ∧ selectOutside T S a b = some c
 | .remaining => selectLarge T S a b = none ∧ selectSizeTwo T S a b = none ∧ selectOutside T S a b = none := by
 unfold selectLocal at h
 split at h
 · rename_i ha
   cases hl : selectLarge T S a b with
   | some e => simp only [hl] at h; cases Option.some.inj h; simp_all
   | none =>
     cases ht : selectSizeTwo T S a b with
     | some c => simp only [hl,ht] at h; cases Option.some.inj h; simp_all
     | none =>
       cases ho : selectOutside T S a b with
       | some c => simp only [hl,ht,ho] at h; cases Option.some.inj h; simp_all
       | none => simp only [hl,ht,ho] at h; cases Option.some.inj h; simp_all
 · contradiction

theorem local_prefix_checks {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (cab : CherryAt T i a b) (sel : selectLocal T S a b = some s) (ready : s ≠ .remaining)
 {c : Child} (hc : c ∈ localChildren S a b s) :
 partitionCheck (leaves S) c.partition = true ∧ pairwiseEmbeddings S c.partition = true ∧
 c.paid = 2 ∧ c.partition.length = 3 := by
 have facts := selectLocal_cases sel
 have parts := admitted_parts facts.1
 have prop := properPair_parts parts.1
 cases s with
 | large e =>
   have ce : c = pendantChild S a b := by simpa [localChildren] using hc
   subst c
   obtain ⟨hp,he,paid⟩ := pendant_checks prop.1 prop.2.1 prop.2.2 cab
   have cost : (pendantChild S a b).paid = 2 := parts.2.2.2.2
   exact ⟨hp,he,cost,by omega⟩
 | two d =>
   have ds := selectSizeTwo_sound facts.2.2
   obtain ⟨_,cpq,_⟩ := sizeTwoCandidate_sound ds
   obtain ⟨Y,Z,hp,he,perm,sep,pX,qX⟩ := admitted_sizeTwo_context facts.1 cab ds
   have labs := hasCherry_labels (actual_hasCherry cpq)
   exact five_checks prop.1 prop.2.1 prop.2.2 cab labs.1 labs.2 sep parts.2.2.2.2 hc
 | outside d =>
   have ds := outsideCandidate_sound (selectOutside_sound facts.2.2.2)
   have labs := hasCherry_labels (actual_hasCherry ds.1)
   exact five_checks prop.1 prop.2.1 prop.2.2 cab labs.1 labs.2 ds.2.2.2.2 parts.2.2.2.2 hc
 | remaining => exact False.elim (ready rfl)

theorem five_materialized {S : Tree} {a b p q : Nat} {c : Child}
 (hc : c ∈ fiveChildren S a b p q) : c.sourceForest = c.partition.filterMap (fun B => restrict B S) := by
 have cs : c = pendantChild S a b ∨ c = pairChild S p a ∨ c = pairChild S p b ∨
   c = pairChild S q a ∨ c = pairChild S q b := by simpa [fiveChildren] using hc
 rcases cs with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem local_prefix_source_forest {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (cab : CherryAt T i a b) (sel : selectLocal T S a b = some s) (ready : s ≠ .remaining)
 {c : Child} (hc : c ∈ localChildren S a b s) :
 c.sourceForest = c.partition.filterMap (fun B => restrict B S) ∧ c.sourceForest.length = 3 := by
 have mat : c.sourceForest = c.partition.filterMap (fun B => restrict B S) := by
   cases s with
   | large e =>
     have ce : c = pendantChild S a b := by simpa [localChildren] using hc
     subst c
     rfl
   | two d => exact five_materialized hc
   | outside d => exact five_materialized hc
   | remaining => exact False.elim (ready rfl)
 have checks := local_prefix_checks cab sel ready hc
 have len := forest_length checks.1
 simp only [makeChild] at len
 exact ⟨mat,by rw [mat,len]; exact checks.2.2.2⟩

/-- The operational dispatcher consumes only the proved source prefix. Every
call keeps its own exact bounded child contract and source budget refusal. -/
theorem local_prefix_child_solver {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (cab : CherryAt T i a b) (sel : selectLocal T S a b = some s) (ready : s ≠ .remaining)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀ c, c ∈ localChildren S a b s → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃ c, c ∈ localChildren S a b s ∧ ∃ G, childCall solver k c = some G := by
 have facts := selectLocal_cases sel
 cases s with
 | large e =>
   have hh := admitted_large_child_solver facts.1 cab facts.2 solver (ih _ (by simp [localChildren])) k
   simpa [localChildren] using hh
 | two c =>
   exact admitted_sizeTwo_child_solver facts.1 cab facts.2.2 solver ih k
 | outside c =>
   exact admitted_outside_child_solver facts.1 cab facts.2.2.2 solver ih k
 | remaining => exact False.elim (ready rfl)

theorem local_prefix_cover {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 {F : List (List Nat)} (cab : CherryAt T i a b) (sel : selectLocal T S a b = some s)
 (ready : s ≠ .remaining) (ha : agreement T S F = true) :
 ∃ c, c ∈ localChildren S a b s ∧ ∃ G, feasible T S c G ∧ G.length ≤ F.length := by
 have facts := selectLocal_cases sel
 cases s with
 | large e =>
   have sc := selectLarge_sound facts.2
   obtain ⟨G,hG,hlen,href⟩ := admitted_large_exchange facts.1 cab sc.1 sc.2.1 sc.2.2 ha
   exact ⟨pendantChild S a b,by simp [localChildren],G,⟨hG,href⟩,hlen⟩
 | two c =>
   obtain ⟨d,hd,hF⟩ := admitted_sizeTwo_cover facts.1 cab facts.2.2 ha
   exact ⟨d,hd,F,hF,Nat.le_refl _⟩
 | outside c =>
   obtain ⟨d,hd,hF⟩ := admitted_outside_cover facts.1 cab facts.2.2.2 ha
   exact ⟨d,hd,F,hF,Nat.le_refl _⟩
 | remaining => exact False.elim (ready rfl)

theorem local_prefix_minimum {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {s : LocalSelection}
 (cab : CherryAt T i a b) (sel : selectLocal T S a b = some s) (ready : s ≠ .remaining)
 (solve : Child → List (List Nat)) (ih : ∀ c, c ∈ localChildren S a b s → ExactChild T S c (solve c))
 (best : List (List Nat)) (chosen : ∃ c, c ∈ localChildren S a b s ∧ best = solve c)
 (least : ∀ c, c ∈ localChildren S a b s → best.length ≤ (solve c).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 obtain ⟨c,hc,rfl⟩ := chosen
 refine ⟨(ih c hc).1.1,?_⟩
 intro F ha
 obtain ⟨d,hd,G,hG,hlen⟩ := local_prefix_cover cab sel ready ha
 exact Nat.le_trans (least d hd) (Nat.le_trans ((ih d hd).2 G hG) hlen)

end Universal233.Rule5Classification
