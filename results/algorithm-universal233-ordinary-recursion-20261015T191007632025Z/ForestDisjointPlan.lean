import ForestLocal
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups
open Universal233 Universal233.PaidQueries Universal233.MafScheduler

def PairValid (m : Tree × Tree → Nat) (p : Tree × Tree) (F : Forest) : Prop :=
  agreement p.1 p.2 F = true ∧ F.length-1 = m p

theorem jobs_planned (t : Tree) (ss : List Tree) (m : Tree × Tree → Nat)
    (actual : ∀ s ∈ ss, componentPair t s = some (pair t s))
    (pp : ∀ s ∈ ss, DepthOne.proper (pair t s).1 (pair t s).2 = true)
    (mm : ∀ s ∈ ss, LocalMinimum (pair t s).1 (pair t s).2 (m (pair t s))) :
    ∃ js, jobs t ss = some js ∧ js.map Job.problem = ss.map (pair t) ∧
      ∀ j ∈ js, Planned m (PairValid m) j := by
  induction ss with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons s ss ih =>
    obtain ⟨tail,ht,hkeys,hplan⟩ := ih
      (fun r hr => actual r (by simp [hr]))
      (fun r hr => pp r (by simp [hr])) (fun r hr => mm r (by simp [hr]))
    have pact := actual s (by simp)
    have pproper := pp s (by simp)
    have pmin := mm s (by simp)
    cases he : DepthOne.pretest01 (pair t s).1 (pair t s).2 with
    | refused =>
      have hr := (DepthOne.refused_iff _ _).1 he
      simp [pproper] at hr
    | rejected =>
      refine ⟨.hard (pair t s) :: tail,by simpa [jobs,pact,he] using congrArg (Option.map (.hard (pair t s) :: ·)) ht,
        by simp [hkeys,Job.problem],?_⟩
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · obtain ⟨F,hF,hcost⟩ := pmin.1
        have hl := DepthOne.rejected_lower_bound _ _ he F hF
        simpa [Planned,←hcost] using hl
      · exact hplan j hj
    | found c =>
      obtain ⟨ha,hcost,hminimal⟩ := DepthOne.found_globally_minimum _ _ c he
      obtain ⟨F,hF,hopt⟩ := pmin.1
      have hlow := pmin.2 _ ha
      have hupp := hminimal F hF
      have hcm : DepthOne.cutCost c = m (pair t s) := by omega
      let j : Job (Tree × Tree) Forest := .resolved (pair t s) (DepthOne.cutCost c) (DepthOne.forest s c)
      refine ⟨j :: tail,by simpa [jobs,pact,he,j] using congrArg (Option.map (j :: ·)) ht,
        by simp [j,hkeys,Job.problem],?_⟩
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · change DepthOne.cutCost c = m (pair t s) ∧ PairValid m (pair t s) (DepthOne.forest s c) ∧ DepthOne.cutCost c ≤ 1
        exact ⟨hcm,⟨ha,hcost.trans hcm⟩,DepthOne.cutCost_le_one c⟩
      · exact hplan k hk

theorem sum_map_le' {α : Type} (L : List α) (f g : α → Nat)
    (h : ∀ x ∈ L, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hh := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    omega

end GenericForest
