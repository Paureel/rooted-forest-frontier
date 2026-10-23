import ForestLocal
import Optimality01

/-! Problem-specific full-current-source-forest depth-zero/one pretest.
The executable entry point enumerates only original source edges and checks
original ForestState.agrees on the entire candidate. -/
namespace ForestPretest01
open RMAF RestrictionBridge ForestState
abbrev Forest := List (List Nat)

def unchanged (ss : List Tree) : Forest := ss.map leaves

def oneCuts : List Tree → List Forest
  | [] => []
  | s :: ss =>
      (Universal233.DepthOne.edges s).map
        (fun p => Universal233.DepthOne.forest s (some p) ++ unchanged ss) ++
      (oneCuts ss).map (leaves s :: ·)

def candidates (ss : List Tree) : List Forest := unchanged ss :: oneCuts ss

inductive Result where
  | refused
  | rejected
  | found (F : Forest)
  deriving DecidableEq, Repr

def pretest01 (T : Option Tree) (ss : List Tree) : Result :=
  if proper T ss then
    match best (additionalCost ss) (agrees T ss) (candidates ss) with
    | none => .rejected
    | some F => .found F
  else .refused

theorem oneCuts_length (ss : List Tree) (F : Forest) (h : F ∈ oneCuts ss) :
    F.length = ss.length + 1 := by
  induction ss generalizing F with
  | nil => simp [oneCuts] at h
  | cons s ss ih =>
    simp only [oneCuts,List.mem_append,List.mem_map] at h
    rcases h with ⟨p,_,rfl⟩ | ⟨G,hG,rfl⟩
    · simp [Universal233.DepthOne.forest,unchanged]
    · have := ih G hG
      simp only [List.length_cons]
      omega

theorem candidate_cost_le_one (ss : List Tree) (F : Forest) (h : F ∈ candidates ss) :
    additionalCost ss F ≤ 1 := by
  rcases List.mem_cons.1 h with he | hm
  · subst F; simp [additionalCost,unchanged]
  · have := oneCuts_length ss F hm
    simp only [additionalCost]
    omega

theorem found_spec (T : Option Tree) (ss : List Tree) (F : Forest)
    (h : pretest01 T ss = .found F) :
    proper T ss = true ∧ F ∈ candidates ss ∧ agrees T ss F = true ∧
      additionalCost ss F ≤ 1 ∧
      ∀ G, G ∈ candidates ss → agrees T ss G = true → additionalCost ss F ≤ additionalCost ss G := by
  unfold pretest01 at h
  split at h
  · rename_i hp
    cases hb : best (additionalCost ss) (agrees T ss) (candidates ss) with
    | none => simp [hb] at h
    | some G =>
      have he : G = F := by simpa [hb] using h
      subst G
      obtain ⟨hm,ha,hmin⟩ := best_spec _ _ _ F hb
      exact ⟨hp,hm,ha,candidate_cost_le_one ss F hm,hmin⟩
  · simp at h

theorem rejected_spec (T : Option Tree) (ss : List Tree)
    (h : pretest01 T ss = .rejected) :
    proper T ss = true ∧ ∀ F, F ∈ candidates ss → agrees T ss F = false := by
  unfold pretest01 at h
  split at h
  · rename_i hp
    cases hb : best (additionalCost ss) (agrees T ss) (candidates ss) with
    | none => exact ⟨hp,(best_none_iff _ _ _).1 hb⟩
    | some F => simp [hb] at h
  · simp at h

theorem refused_iff (T : Option Tree) (ss : List Tree) :
    pretest01 T ss = .refused ↔ proper T ss = false := by
  unfold pretest01
  cases hp : proper T ss <;> simp [hp]
  cases best (additionalCost ss) (agrees T ss) (candidates ss) <;> simp

end ForestPretest01
