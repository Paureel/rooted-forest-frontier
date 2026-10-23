-- Same contacted lineage: derive the actual hard2 entry domain from computation.
import Hard2ControlsV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentOneExchange ContactedForward
namespace ContactedHard2

theorem selected_hard2_original {T S : Tree} {c : Candidate} (selected : select T S=some (.hard2,c)) :
 CoreGraph.CherryAt T c.parent c.a c.b ∧ c.originalCuts=cuts S c.a c.b ∧ c.originalCuts.length=2 := by
 cases zero : (candidates T S).find? (fun x=>x.originalCuts.isEmpty) with
 | some e => simp only [select,zero] at selected;cases selected
 | none =>
  cases one : (candidates T S).find? (fun x=>x.originalCuts.length == 1) with
  | some e => simp only [select,zero,one] at selected;cases selected
  | none =>
   cases high : (candidates T S).find? (fun x=>3≤x.originalCuts.length) with
   | some e => simp only [select,zero,one,high] at selected;cases selected
   | none =>
    cases head : (candidates T S).head? with
    | none => simp only [select,zero,one,high,head,Option.map_none] at selected;cases selected
    | some e =>
     have eq : e=c := (Prod.mk.inj (Option.some.inj (by simpa only [select,zero,one,high,head,Option.map_some] using selected))).2
     subst e
     have member := List.mem_of_head? head
     have actual := ContactedOneConsumer.candidate_original member
     have nz := List.find?_eq_none.1 zero c member
     have no := List.find?_eq_none.1 one c member
     have nh := List.find?_eq_none.1 high c member
     have positive : c.originalCuts≠[] := by intro h;simp only [h,List.isEmpty_nil] at nz;exact nz True.intro
     have nzero : c.originalCuts.length≠0 := fun h=>positive (List.length_eq_zero_iff.1 h)
     have none : c.originalCuts.length≠1 := by simpa only [beq_iff_eq] using no
     have nlarge : ¬3≤c.originalCuts.length := by simpa only [decide_eq_true_eq] using nh
     exact ⟨actual.1,actual.2,by omega⟩

theorem early_hard2_saved {T S : Tree} {c d : Candidate}
 (selected : early T S=.hard2 c d) :
 select T S=some (.hard2,c) ∧ select S T=some (.hard2,d) ∧
 Rule4.select T S=none ∧ Rule4.select S T=none := by
 cases fwd : select T S with
 | none =>
  cases rev : select S T with
  | none => simp only [early,fwd,rev] at selected;cases selected
  | some pair =>
   rcases pair with ⟨priority,e⟩
   cases priority <;> simp only [early,fwd,rev] at selected <;> cases selected
 | some pair =>
  rcases pair with ⟨priority,e⟩
  cases rev : select S T with
  | none => cases priority <;> simp only [early,fwd,rev] at selected <;> cases selected
  | some pair =>
   rcases pair with ⟨priorityR,f⟩
   cases priority <;> cases priorityR <;> simp only [early,fwd,rev] at selected
   all_goals first
    | cases selected
    | (cases a : Rule4.select T S <;> simp only [a] at selected
       all_goals first
        | (cases b : Rule4.select S T <;> simp only [b] at selected
           all_goals first
            | (cases selected;exact ⟨rfl,rfl,rfl,rfl⟩)
            | cases selected)
        | cases selected)

theorem actual_hard2_domain {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d) :
 DepthOne.proper T S=true ∧
 (CoreGraph.CherryAt T c.parent c.a c.b ∧ c.originalCuts=cuts S c.a c.b ∧ c.originalCuts.length=2) ∧
 (CoreGraph.CherryAt S d.parent d.a d.b ∧ d.originalCuts=cuts T d.a d.b ∧ d.originalCuts.length=2) ∧
 Rule4.select T S=none ∧ Rule4.select S T=none := by
 have saved := early_hard2_saved selected
 exact ⟨proper,selected_hard2_original saved.1,selected_hard2_original saved.2.1,saved.2.2⟩
end ContactedHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2.selected_hard2_original
#print axioms ContactedHard2.selected_hard2_original
#check @ContactedHard2.early_hard2_saved
#print axioms ContactedHard2.early_hard2_saved
#check @ContactedHard2.actual_hard2_domain
#print axioms ContactedHard2.actual_hard2_domain
