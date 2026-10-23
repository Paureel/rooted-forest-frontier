import OutputGroupedCaller
import BadGroupedPair
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem own_best_sound {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α) (b : α)
 (run : best cost valid xs=some b) : valid b=true ∧ b∈xs := by
 induction xs with
 | nil=>cases run
 | cons a xs ih=>
  by_cases va : valid a=true
  · cases tail : best cost valid xs with
    | none=>
     have eq : a=b:=Option.some.inj (by simpa only [best,va,ite_true,tail] using run)
     subst b
     exact ⟨va,List.mem_cons_self⟩
    | some c=>
     by_cases le : cost a≤cost c
     · have eq : a=b:=Option.some.inj (by simpa only [best,va,ite_true,tail,ite_eq_left le] using run)
       subst b;exact ⟨va,List.mem_cons_self⟩
     · have eq : c=b:=Option.some.inj (by simpa only [best,va,ite_true,tail,ite_eq_right le] using run)
       subst b
       exact ⟨(ih tail).1,List.mem_cons_of_mem _ (ih tail).2⟩
  · have tailRun : best cost valid xs=some b:=by simpa only [best,ite_eq_right va] using run
    exact ⟨(ih tailRun).1,List.mem_cons_of_mem _ (ih tailRun).2⟩

theorem own_best_complete {α : Type} (cost : α→Nat) (valid : α→Bool) (xs : List α) (a : α)
 (member : a∈xs) (va : valid a=true) :
 ∃b,best cost valid xs=some b ∧ valid b=true ∧ cost b≤cost a := by
 induction xs with
 | nil=>simp at member
 | cons c xs ih=>
  rcases List.mem_cons.mp member with eq|tailMember
  · subst c
    cases tail : best cost valid xs with
    | none=>exact ⟨a,by simp only [best,va,ite_true,tail],va,Nat.le_refl _⟩
    | some b=>
     by_cases le : cost a≤cost b
     · exact ⟨a,by simp only [best,va,ite_true,tail,ite_eq_left le],va,Nat.le_refl _⟩
     · exact ⟨b,by simp only [best,va,ite_true,tail,ite_eq_right le],(own_best_sound cost valid xs b tail).1,by omega⟩
  · obtain ⟨b,runB,validB,least⟩:=ih tailMember
    by_cases vc : valid c=true
    · by_cases le : cost c≤cost b
      · exact ⟨c,by simp only [best,vc,ite_true,runB,ite_eq_left le],vc,Nat.le_trans le least⟩
      · exact ⟨b,by simp only [best,vc,ite_true,runB,ite_eq_right le],validB,least⟩
    · exact ⟨b,by simpa only [best,ite_eq_right vc] using runB,validB,least⟩

theorem grouped_evaluate_member (actual : BothBadLocal.Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat)
 (outs : List Output) (o : Output) (member : o∈outs) (G : List (List Nat))
 (runG : (BothBadGrouped.runOutput actual T S A B C q o).answer?=some G) :
 G∈(BothBadGrouped.evaluate actual T S A B C q outs).candidates := by
 induction outs with
 | nil=>simp at member
 | cons a outs ih=>
  rcases List.mem_cons.mp member with eq|tail
  · subst a
    change G∈(BothBadGrouped.runOutput actual T S A B C q o).answer?.toList++_
    rw [runG]
    exact List.mem_append.mpr (Or.inl List.mem_cons_self)
  · exact List.mem_append.mpr (Or.inr (ih tail))

theorem bothbad_literal_outputs (S : Tree) (A B D : List Nat) (q : Nat) :
 BothBad.outputs S A B D q=sideOutputs S B A D q++sideOutputs S A B D q := by rfl

theorem bothbad_output_scope (T S : Tree) (A B C : List Nat) (D : List Nat) (q : Nat)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (swapped : partitionCheck (leaves S) [B,A,C]=true) (o : Output)
 (member : o∈BothBad.outputs S A B D q) (real : CutRealization.RealizedOutput S o) :
 partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
 VertexGeometry.Refines o.partition [A,B,C] ∧ o.partition.length=o.sourceCuts.length+1 ∧ 0<o.sourceCuts.length := by
 rw [bothbad_literal_outputs] at member
 rcases List.mem_append.mp member with left|right
 · have pay:=whole_source_payment T S B A C q (fun _=>0) (sideColor D) (fun _=>0) proper swapped o left real
   have ref:=tagged_output_refines T S B A C (fun _=>0) (sideColor D) (fun _=>0) q proper swapped o left
   refine ⟨pay.1,pay.2.1,?_,pay.2.2.1,by have bound:=pay.2.2.2;omega⟩
   intro K kP
   obtain ⟨U,uP,sub⟩:=ref K kP
   exact ⟨U,(List.Perm.swap A B [C]).mem_iff.mp uP,sub⟩
 · have pay:=whole_source_payment T S A B C q (fun _=>0) (sideColor D) (fun _=>0) proper parents o right real
   have ref:=tagged_output_refines T S A B C (fun _=>0) (sideColor D) (fun _=>0) q proper parents o right
   exact ⟨pay.1,pay.2.1,ref,pay.2.2.1,by have bound:=pay.2.2.2;omega⟩

theorem bothbad_grouped_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex)
 (below : PaidInstances.BelowBudget ordinary q) (proper : DepthOne.proper T S=true)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (swapped : partitionCheck (leaves S) [B,A,C]=true)
 (ac : Clear (minimalVertices A T) (minimalVertices C T)) (bc : Clear (minimalVertices B T) (minimalVertices C T))
 (edge : e∈PairGeometry.edges T) (F : List (List Nat)) (agree : agreement T S F=true)
 (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q) :
 ∃G,(BothBadGrouped.executePair (PaidInstances.OwnPaid ordinary q) T S A B C e q).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 obtain ⟨o,member,refF,real⟩:=bothbad_source_cover T S A B C q e F proper parents agree ref budget edge swapped
 have originalMember : o∈BothBad.outputs S A B (PairGeometry.descendants T e.2) q := by
  rw [bothbad_literal_outputs];exact member
 have os:=bothbad_output_scope T S A B C (PairGeometry.descendants T e.2) q proper parents swapped o originalMember real
 obtain ⟨H,runH,agreeH,leastH⟩:=output_grouped_answer ordinary q T S A B C o below proper parents
  os.1 os.2.1 os.2.2.1 os.2.2.2.1 os.2.2.2.2 ac bc F agree refF budget
 have inCandidates:=grouped_evaluate_member (PaidInstances.OwnPaid ordinary q) T S A B C q _ o originalMember H runH
 have acceptedH : BothBadGrouped.accepted T S q H=true := by
  simp only [BothBadGrouped.accepted,agreeH,decide_eq_true (show H.length-1≤q by omega),Bool.and_self]
 obtain ⟨G,runG,acceptedG,leastG⟩:=own_best_complete List.length (BothBadGrouped.accepted T S q) _ H inCandidates acceptedH
 have agreeG : agreement T S G=true := by
  have checks:=acceptedG
  simp only [BothBadGrouped.accepted,Bool.and_eq_true] at checks
  exact checks.1
 exact ⟨G,runG,agreeG,Nat.le_trans leastG leastH⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.own_best_sound
#print axioms ContactedHard2Survival.own_best_sound
#check @ContactedHard2Survival.own_best_complete
#print axioms ContactedHard2Survival.own_best_complete
#check @ContactedHard2Survival.grouped_evaluate_member
#print axioms ContactedHard2Survival.grouped_evaluate_member
#check @ContactedHard2Survival.bothbad_literal_outputs
#print axioms ContactedHard2Survival.bothbad_literal_outputs
#check @ContactedHard2Survival.bothbad_output_scope
#print axioms ContactedHard2Survival.bothbad_output_scope
#check @ContactedHard2Survival.bothbad_grouped_cover
#print axioms ContactedHard2Survival.bothbad_grouped_cover
