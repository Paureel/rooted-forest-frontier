import SourceColorCover
import Dispatcher
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem original_checked_sound {T S : Tree} {q : Nat} {o : Option BothBad.Forest} {F : BothBad.Forest}
 (h : BothBad.checked T S q o=some F) : agreement T S F=true ∧ F.length-1≤q := by
 exact ContactedGoodPair.checked_sound h

theorem choose_left_no_larger (F : BothBad.Forest) (b : Option BothBad.Forest) :
 ∃G,BothBad.choose (some F) b=some G ∧ G.length≤F.length := by
 cases b with
 | none => exact ⟨F,rfl,Nat.le_refl _⟩
 | some H =>
  by_cases h : F.length≤H.length
  · exact ⟨F,by simp only [BothBad.choose,ite_eq_left h],Nat.le_refl _⟩
  · exact ⟨H,by simp only [BothBad.choose,ite_eq_right h],by omega⟩

theorem choose_right_no_larger (a : Option BothBad.Forest) (F : BothBad.Forest) :
 ∃G,BothBad.choose a (some F)=some G ∧ G.length≤F.length := by
 cases a with
 | none => exact ⟨F,rfl,Nat.le_refl _⟩
 | some H =>
  by_cases h : H.length≤F.length
  · exact ⟨H,by simp only [BothBad.choose,ite_eq_left h],h⟩
  · exact ⟨F,by simp only [BothBad.choose,ite_eq_right h],Nat.le_refl _⟩

theorem choose_some_source (a b : Option BothBad.Forest) (F : BothBad.Forest)
 (h : BothBad.choose a b=some F) : a=some F ∨ b=some F := by
 cases a with
 | none => exact Or.inr h
 | some G =>
  cases b with
  | none => exact Or.inl h
  | some H =>
   by_cases le : G.length≤H.length
   · exact Or.inl (by simpa only [BothBad.choose,ite_eq_left le] using h)
   · exact Or.inr (by simpa only [BothBad.choose,ite_eq_right le] using h)

theorem execute_some_sound (solve : BothBad.ForestSolver) (T S : Tree) (q : Nat) (es : List BothBad.Entry) (F : BothBad.Forest)
 (h : (BothBad.execute solve T S q es).answer=some F) : agreement T S F=true ∧ F.length-1≤q := by
 induction es with
 | nil => simp only [BothBad.execute] at h;cases h
 | cons e es ih =>
  change BothBad.choose (BothBad.checked T S q (BothBad.dispatch solve T S e).answer)
   (BothBad.execute solve T S q es).answer=some F at h
  rcases choose_some_source _ _ _ h with ha|hb
  · exact original_checked_sound ha
  · exact ih hb

theorem execute_member_no_larger (solve : BothBad.ForestSolver) (T S : Tree) (q : Nat)
 (es : List BothBad.Entry) (e : BothBad.Entry) (member : e∈es) (F : BothBad.Forest)
 (h : BothBad.checked T S q (BothBad.dispatch solve T S e).answer=some F) :
 ∃G,(BothBad.execute solve T S q es).answer=some G ∧ G.length≤F.length := by
 induction es with
 | nil => simp at member
 | cons a es ih =>
  change ∃G,BothBad.choose (BothBad.checked T S q (BothBad.dispatch solve T S a).answer)
   (BothBad.execute solve T S q es).answer=some G ∧ G.length≤F.length
  rcases List.mem_cons.mp member with eq|tail
  · subst a
    rw [h]
    exact choose_left_no_larger F _
  · obtain ⟨G,runG,bound⟩:=ih tail
    rw [runG]
    obtain ⟨H,runH,least⟩:=choose_right_no_larger (BothBad.checked T S q (BothBad.dispatch solve T S a).answer) G
    exact ⟨H,runH,Nat.le_trans least bound⟩

theorem literal_full_dispatch_complete (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (below : PaidInstances.BelowBudget ordinary q) (proper : DepthOne.proper T S=true)
 (o : Output) (part : partitionCheck (leaves S) o.partition=true) (emb : pairwiseEmbeddings S o.partition=true)
 (payment : o.partition.length=o.sourceCuts.length+1) (positive : 0<o.sourceCuts.length)
 (F : List (List Nat)) (agree : agreement T S F=true) (ref : VertexGeometry.Refines F o.partition)
 (budget : F.length-1≤q) :
 o.sourceCuts.length≤q ∧ q-o.sourceCuts.length<q ∧
 ∃G,BothBad.checked T S q (BothBad.dispatch (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) T S
  ⟨o,.full,q-o.sourceCuts.length⟩).answer=some G ∧ agreement T S G=true ∧ G.length≤F.length := by
 have scope:=FreshResidual.residual_transfer_scope.1 T S o.partition F proper part emb
 have fa : agrees (some T) (OutputState.sourceForest S o.partition) F=true := scope.2.2.mpr ⟨agree,ref⟩
 have count:=sources_le_blocks _ _ _ fa
 have paid : o.sourceCuts.length≤q ∧ q-o.sourceCuts.length<q ∧
  additionalCost (OutputState.sourceForest S o.partition) F≤q-o.sourceCuts.length := by
  unfold additionalCost
  rw [scope.1] at *
  omega
 have ih:=PaidInstances.local_ordinary_ih ordinary q (q-o.sourceCuts.length) below paid.2.1
 obtain ⟨G,runG,least⟩:=PaidInstanceForest.forest_completion_obligation (q-o.sourceCuts.length)
  (PaidInstances.OwnPaid ordinary q) ih (some T) (OutputState.sourceForest S o.partition) F fa paid.2.2
 have global:=(FreshResidual.residual_transfer_scope.1 T S o.partition G proper part emb).2.2.mp (GenericForest.solve_sound (PaidInstances.OwnPaid ordinary q) _ _ _ G runG).1
 have bg : G.length-1≤q := by omega
 refine ⟨paid.1,paid.2.1,G,?_,global.1,least⟩
 simp only [BothBad.dispatch,runG,BothBad.checked,Option.bind_some,BothBad.accept,global.1,
  decide_eq_true bg,Bool.and_self,ite_true]

theorem literal_full_execute_complete (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (below : PaidInstances.BelowBudget ordinary q) (proper : DepthOne.proper T S=true)
 (outs : List Output) (o : Output) (member : o∈outs)
 (part : partitionCheck (leaves S) o.partition=true) (emb : pairwiseEmbeddings S o.partition=true)
 (payment : o.partition.length=o.sourceCuts.length+1) (positive : 0<o.sourceCuts.length)
 (F : List (List Nat)) (agree : agreement T S F=true) (ref : VertexGeometry.Refines F o.partition)
 (budget : F.length-1≤q) :
 ∃G,(BothBad.execute (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) T S q (BothBad.entries q .full outs)).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 obtain ⟨affordable,strict,H,runH,_,leastH⟩:=literal_full_dispatch_complete ordinary q T S below proper o part emb payment positive F agree ref budget
 let e : BothBad.Entry:=⟨o,.full,q-o.sourceCuts.length⟩
 have emem : e∈BothBad.entries q .full outs := by
  apply List.mem_filterMap.mpr
  refine ⟨o,member,?_⟩
  have guard : o.sourceCuts.length+BothBad.Mode.extra .full≤q := by simpa only [BothBad.Mode.extra,Nat.add_zero] using affordable
  rw [ite_eq_left guard]
  rfl
 obtain ⟨G,runG,leastG⟩:=execute_member_no_larger (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) T S q _ e emem H runH
 exact ⟨G,runG,(execute_some_sound _ _ _ _ _ _ runG).1,Nat.le_trans leastG leastH⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_checked_sound
#print axioms ContactedHard2Survival.original_checked_sound
#check @ContactedHard2Survival.choose_left_no_larger
#print axioms ContactedHard2Survival.choose_left_no_larger
#check @ContactedHard2Survival.choose_right_no_larger
#print axioms ContactedHard2Survival.choose_right_no_larger
#check @ContactedHard2Survival.choose_some_source
#print axioms ContactedHard2Survival.choose_some_source
#check @ContactedHard2Survival.execute_some_sound
#print axioms ContactedHard2Survival.execute_some_sound
#check @ContactedHard2Survival.execute_member_no_larger
#print axioms ContactedHard2Survival.execute_member_no_larger
#check @ContactedHard2Survival.literal_full_dispatch_complete
#print axioms ContactedHard2Survival.literal_full_dispatch_complete
#check @ContactedHard2Survival.literal_full_execute_complete
#print axioms ContactedHard2Survival.literal_full_execute_complete
