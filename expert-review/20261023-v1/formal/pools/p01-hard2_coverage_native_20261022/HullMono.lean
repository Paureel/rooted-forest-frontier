import CladeProfile
namespace FreshClade
open RMAF
theorem subset_empty {α : Type} {A : List α} (h : A⊆[]) : A=[] := by
 cases A with
 | nil => rfl
 | cons a A => exact False.elim (by have := h (by simp : a∈a::A); simpa using this)

theorem span_mono (C B : List Nat) (h : ∀x, x∈C → x∈B) (T : Tree) :
 rootedSpan C T ⊆ rootedSpan B T := by
 induction T with
 | leaf x =>
   by_cases hc : x∈C
   · have hb := h x hc; simp [rootedSpan,hc,hb]
   · simp [rootedSpan,hc]
 | node l r il ir =>
   have el : rootedSpan B l=[] → rootedSpan C l=[] := fun he => subset_empty (by simpa [he] using il)
   have er : rootedSpan B r=[] → rootedSpan C r=[] := fun he => subset_empty (by simpa [he] using ir)
   by_cases cl : rootedSpan C l=[] <;> by_cases cr : rootedSpan C r=[] <;>
    by_cases bl : rootedSpan B l=[] <;> by_cases br : rootedSpan B r=[]
   all_goals
    simp_all [rootedSpan,prependSide,List.isEmpty_iff,List.Subset]
    try grind

theorem min_span (C : List Nat) (T : Tree) : minimalVertices C T ⊆ rootedSpan C T := by
 induction T with
 | leaf x => simp [minimalVertices,rootedSpan]
 | node l r il ir =>
   by_cases cl : rootedSpan C l=[] <;> by_cases cr : rootedSpan C r=[]
   all_goals
    have el : rootedSpan C l=[] → minimalVertices C l=[] := span_empty_min_empty C l
    have er : rootedSpan C r=[] → minimalVertices C r=[] := span_empty_min_empty C r
    simp_all [rootedSpan,minimalVertices,prependSide,List.isEmpty_iff,List.Subset]
    try grind

theorem min_mono (C B : List Nat) (h : ∀x, x∈C → x∈B) (T : Tree) :
 minimalVertices C T ⊆ minimalVertices B T := by
 induction T with
 | leaf x =>
   by_cases hc : x∈C
   · have hb := h x hc; simp [minimalVertices,hc,hb]
   · simp [minimalVertices,hc]
 | node l r il ir =>
   have sl := span_mono C B h l
   have sr := span_mono C B h r
   have ml := min_span C l
   have mr := min_span C r
   have el : rootedSpan B l=[] → rootedSpan C l=[] := fun he => subset_empty (by simpa [he] using sl)
   have er : rootedSpan B r=[] → rootedSpan C r=[] := fun he => subset_empty (by simpa [he] using sr)
   by_cases cl : rootedSpan C l=[] <;> by_cases cr : rootedSpan C r=[] <;>
    by_cases bl : rootedSpan B l=[] <;> by_cases br : rootedSpan B r=[]
   all_goals
    have cml : rootedSpan C l=[] → minimalVertices C l=[] := span_empty_min_empty C l
    have cmr : rootedSpan C r=[] → minimalVertices C r=[] := span_empty_min_empty C r
    simp_all [minimalVertices,prependSide,List.isEmpty_iff,List.Subset]
    try grind

theorem disjoint_mono {A B C D : List Nat} {T : Tree}
 (ha : ∀x, x∈A → x∈B) (hc : ∀x, x∈C → x∈D)
 (hd : disjointVertices (minimalVertices B T) (minimalVertices D T)=true) :
 disjointVertices (minimalVertices A T) (minimalVertices C T)=true := by
 rw [disjoint_eq_not_hits] at hd ⊢
 have ha' := min_mono A B ha T
 have hc' := min_mono C D hc T
 cases he : hits (minimalVertices A T) (minimalVertices C T)
 · rfl
 · rcases (hits_true _ _).mp he with ⟨v,hv,hw⟩
   have bad := (hits_true _ _).mpr ⟨v,ha' hv,hc' hw⟩
   simp [bad] at hd
end FreshClade

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshClade.subset_empty
#print axioms FreshClade.subset_empty
#check @FreshClade.span_mono
#print axioms FreshClade.span_mono
#check @FreshClade.min_span
#print axioms FreshClade.min_span
#check @FreshClade.min_mono
#print axioms FreshClade.min_mono
#check @FreshClade.disjoint_mono
#print axioms FreshClade.disjoint_mono
