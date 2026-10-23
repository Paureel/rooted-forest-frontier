/- Contacted derivation of literal .one domain, no author selector reflection. -/
import SelectedControlsV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentOneExchange ContactedRepair ContactedSource
namespace ContactedOneConsumer

theorem enumerated_cherry (T : Tree) : ∀p a b,(p,a,b)∈cherries T→CoreGraph.CherryAt T p a b := by
 induction T with
 | leaf x => intro p a b member;cases member
 | node l r il ir =>
  intro p a b member
  cases l with
  | leaf x =>
   cases r with
   | leaf y =>
    have eq : (p,a,b)=([],x,y) := by simpa only [cherries,List.mem_singleton] using member
    cases eq;rfl
   | node u v =>
    have choices : ∃q c d,(q,c,d)∈cherries (.node u v) ∧ (true::q,c,d)=(p,a,b) := by
     simpa only [cherries,List.map_nil,List.nil_append,List.mem_map,Prod.exists] using member
    obtain ⟨q,c,d,hq,eq⟩ := choices
    cases eq
    exact ir _ _ _ hq
  | node u v =>
   have choices : (∃q c d,(q,c,d)∈cherries (.node u v) ∧ (false::q,c,d)=(p,a,b)) ∨
     (∃q c d,(q,c,d)∈cherries r ∧ (true::q,c,d)=(p,a,b)) := by
    simpa only [cherries,List.mem_append,List.mem_map,Prod.exists] using member
   rcases choices with ⟨q,c,d,hq,eq⟩|⟨q,c,d,hq,eq⟩
   · cases eq;exact il _ _ _ hq
   · cases eq;exact ir _ _ _ hq

theorem candidate_original {T S : Tree} {c : Candidate} (member : c∈candidates T S) :
 CoreGraph.CherryAt T c.parent c.a c.b ∧ c.originalCuts=cuts S c.a c.b := by
 obtain ⟨⟨p,a,b⟩,hc,eq⟩ := List.mem_map.1 member
 cases eq
 exact ⟨enumerated_cherry T p a b hc,rfl⟩

theorem selected_one_original {T S : Tree} {c : Candidate} (selected : select T S=some (.one,c)) :
 CoreGraph.CherryAt T c.parent c.a c.b ∧ c.originalCuts=cuts S c.a c.b ∧ (cuts S c.a c.b).length=1 := by
 cases zero : (candidates T S).find? (fun x=>x.originalCuts.isEmpty) with
 | some d => simp only [select,zero] at selected;cases selected
 | none =>
  cases one : (candidates T S).find? (fun x=>x.originalCuts.length == 1) with
  | some d =>
   have eq : d=c := (Prod.mk.inj (Option.some.inj (by simpa only [select,zero,one] using selected))).2
   subst d
   have actual := candidate_original (List.mem_of_find?_eq_some one)
   have count : c.originalCuts.length=1 := beq_iff_eq.1 (List.find?_some (p:=fun x : Candidate=>x.originalCuts.length == 1) one)
   exact ⟨actual.1,actual.2,by rw [←actual.2];exact count⟩
  | none =>
   cases high : (candidates T S).find? (fun x=>3≤x.originalCuts.length) with
   | some d => simp only [select,zero,one,high] at selected;cases selected
   | none =>
    cases head : (candidates T S).head? <;> simp only [select,zero,one,high,head,Option.map_none,Option.map_some] at selected
    all_goals cases selected

theorem early_one_selected {T S : Tree} {reverse : Bool} {c : Candidate}
 (selected : early T S=.one reverse c) :
 select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.one,c) := by
 cases fwd : select T S with
 | none =>
  cases rev : select S T with
  | none => simp only [early,fwd,rev] at selected;cases selected
  | some pair =>
   rcases pair with ⟨priority,d⟩
   cases priority <;> simp only [early,fwd,rev] at selected
   all_goals cases selected <;> exact rev
 | some pair =>
  rcases pair with ⟨priority,d⟩
  cases rev : select S T with
  | none =>
   cases priority <;> simp only [early,fwd,rev] at selected
   all_goals cases selected <;> exact fwd
  | some pair =>
   rcases pair with ⟨priorityR,e⟩
   cases priority <;> cases priorityR <;> simp only [early,fwd,rev] at selected
   all_goals first
    | (cases selected <;> assumption)
    | (cases a : Rule4.select T S <;> simp only [a] at selected
       all_goals first
        | cases selected
        | (cases b : Rule4.select S T <;> simp only [b] at selected <;> cases selected))

theorem actual_one_domain {T S : Tree} {reverse : Bool} {c : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.one reverse c) :
 DepthOne.proper (Oriented reverse T S).1 (Oriented reverse T S).2=true ∧
 CoreGraph.CherryAt (Oriented reverse T S).1 c.parent c.a c.b ∧
 c.originalCuts=cuts (Oriented reverse T S).2 c.a c.b ∧
 (cuts (Oriented reverse T S).2 c.a c.b).length=1 := by
 have domain := selected_one_original (early_one_selected selected)
 have oriented : DepthOne.proper (Oriented reverse T S).1 (Oriented reverse T S).2=true := by
  cases reverse
  · exact proper
  · change DepthOne.proper S T=true
    obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
    simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
     And.intro ns (And.intro nt perm.symm)
 exact ⟨oriented,domain⟩
end ContactedOneConsumer

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedOneConsumer.enumerated_cherry
#print axioms ContactedOneConsumer.enumerated_cherry
#check @ContactedOneConsumer.candidate_original
#print axioms ContactedOneConsumer.candidate_original
#check @ContactedOneConsumer.selected_one_original
#print axioms ContactedOneConsumer.selected_one_original
#check @ContactedOneConsumer.early_one_selected
#print axioms ContactedOneConsumer.early_one_selected
#check @ContactedOneConsumer.actual_one_domain
#print axioms ContactedOneConsumer.actual_one_domain
