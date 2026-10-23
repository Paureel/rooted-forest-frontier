import FreshComparisons
open RMAF Universal233.CoreGraph Universal233.CoreProgram Universal233.Integration
namespace IntegrationScopeWitnesses

-- Post-contact source-scope witnesses, independently confirmed against actual code.
-- These are not retrospectively preregistered controls or extra replications.
def quartet : Tree := .node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3)))
theorem dropping_embedding_guard_fails :
    RMAF.partitionCheck (leaves quartet) [[0,2],[1,3]] = true ∧
    RMAF.pairwiseEmbeddings quartet [[0,2],[1,3]] = false := by decide

theorem homogeneous_projection_is_not_injective :
    groups (normalize (fromTree (fun _ => 7) [] (.node (.leaf 5) (.leaf 9)))) = [⟨[],[5,9],7⟩] ∧
    cherryProjection [] [false] = cherryProjection [] [true] := by decide

def pair : Tree := .node (.leaf 0) (.leaf 1)
theorem budget_zero_local_success_without_output :
    erase [false] (fromTree id [] pair) = some (.leaf ⟨[true],[1],1⟩) ∧
    (generate pair id 0).outputs = [] ∧
    (generate pair id 0).refusals = [] ∧
    (generate pair id 0).visited = 1 ∧
    (generate pair id 0).childAttempts = 1 ∧
    (generate pair id 0).pruned = 1 := by decide

def chain : Tree := .node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4))))
def parity (x : Nat) := x % 2
def target : List (List Nat) := [[0,2,4],[1],[3]]
theorem one_target_singleton_not_both :
    RMAF.partitionCheck (leaves chain) target = true ∧
    RMAF.pairwiseEmbeddings chain target = true ∧
    FreshIntegrationChecks.choiceView (choose (normalize (fromTree parity [] chain))) =
      (2, [[true,true,true,false],[true,true,true,true]]) ∧
    target.contains [3] = true ∧ target.contains [4] = false := by decide

def forged : GTree := .node [] (.leaf ⟨[false,false,false],[0],0⟩) (.leaf ⟨[true],[1],1⟩)
def marker (_ : GTree) (_ : List Group) (_ : List Vertex) : Receipt := ⟨[],[],17,0,0⟩
theorem local_origin_guards_do_not_imply_named_original_reachability :
    (origins forged).Nodup ∧ RootZeroOnly forged ∧
    (subtree pair [false,false,false] = none) ∧
    (attempt marker forged [] [] ⟨[false,false,false],[0],0⟩).visited = 17 := by decide
theorem forged_empty_cuts_avoid : CutsAvoid forged [] := by
  intro v hv
  simp at hv

theorem proper_label_generate_guard_is_separate :
    RMAF.partitionCheck [0,0] [[0]] = true ∧
    RMAF.pairwiseEmbeddings (.node (.leaf 0) (.leaf 0)) [[0]] = true ∧
    (generate (.node (.leaf 0) (.leaf 0)) id 3).refusals = ["duplicate original label"] ∧
    (generate (.node (.leaf 0) (.leaf 0)) id 3).outputs = [] := by decide
end IntegrationScopeWitnesses
