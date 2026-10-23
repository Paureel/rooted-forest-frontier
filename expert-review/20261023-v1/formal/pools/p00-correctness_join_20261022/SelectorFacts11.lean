-- Own selector reconstruction from the actual staged definitions only.
import BranchGeometry34
import EarlySelector
open RMAF Universal233 CherryBranching OrdinaryDispatch FastOrdinary
namespace HighSelector
theorem cherry_of_enum (T : Tree) (p : RMAF.Vertex) (a b : Nat)
    (h : (p,a,b) ∈ cherries T) : CoreGraph.CherryAt T p a b := by
  induction T generalizing p a b with
  | leaf x => simp only [cherries,List.not_mem_nil] at h
  | node L R ihL ihR =>
    cases L <;> cases R
    · simp only [cherries,List.mem_singleton,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      rfl
    all_goals
      simp only [cherries,List.mem_append,List.mem_map] at h
      rcases h with ⟨⟨q,x,y⟩,hx,he⟩ | ⟨⟨q,x,y⟩,hx,he⟩
      · cases he
        simpa only [CoreGraph.CherryAt,CoreGraph.subtree,Bool.false_eq_true,ite_false,ite_true] using ihL q x y hx
      · cases he
        simpa only [CoreGraph.CherryAt,CoreGraph.subtree,Bool.false_eq_true,ite_false,ite_true] using ihR q x y hx
theorem candidate_fields (T S : Tree) (c : Candidate) (h : c ∈ candidates T S) :
    CoreGraph.CherryAt T c.parent c.a c.b ∧ c.originalCuts=cuts S c.a c.b := by
  obtain ⟨⟨p,a,b⟩,hm,he⟩ := List.mem_map.mp h
  cases he
  exact ⟨cherry_of_enum T p a b hm,rfl⟩
theorem selected_high (T S : Tree) (c : Candidate) (h : select T S=some (.high,c)) :
    c ∈ candidates T S ∧ 3≤c.originalCuts.length := by
  unfold select at h
  dsimp only at h
  split at h
  · cases congrArg Prod.fst (Option.some.inj h)
  · split at h
    · cases congrArg Prod.fst (Option.some.inj h)
    · split at h
      next d hd =>
        have he : d=c := congrArg Prod.snd (Option.some.inj h)
        subst d
        have hl : decide (3≤c.originalCuts.length)=true := List.find?_some (p:=fun d : Candidate => decide (3≤d.originalCuts.length)) hd
        exact ⟨List.mem_of_find?_eq_some hd,of_decide_eq_true hl⟩
      next hn =>
        cases hc : (candidates T S).head? with
        | none => simp only [hc,Option.map_none] at h; cases h
        | some d =>
          simp only [hc,Option.map_some] at h
          cases congrArg Prod.fst (Option.some.inj h)
theorem proper_swap (T S : Tree) (h : DepthOne.proper T S=true) : DepthOne.proper S T=true := by
  simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at *
  exact ⟨⟨h.1.2,h.1.1⟩,h.2.symm⟩
theorem proper_oriented (T S : Tree) (r : Bool) (h : DepthOne.proper T S=true) :
    DepthOne.proper (Oriented r T S).1 (Oriented r T S).2=true := by
  cases r
  · exact h
  · exact proper_swap T S h
end HighSelector
