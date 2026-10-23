import CheapProbeEmbedding
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem literal_retained_dispatch_complete (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (A B C : List Nat) (p : RMAF.Vertex) (o : Output) (J : List (List Nat)) (known F : List (List Nat))
 (below : PaidInstances.BelowBudget ordinary q) (proper : DepthOne.proper T S=true)
 (parents : partitionCheck (leaves S) [A,B,C]=true)
 (part : partitionCheck (leaves S) o.partition=true) (emb : pairwiseEmbeddings S o.partition=true)
 (refP : VertexGeometry.Refines o.partition [A,B,C]) (payment : o.partition.length=o.sourceCuts.length+1)
 (oneA : (owned (sourceForest S o.partition) A).length=1)
 (oneC : (owned (sourceForest S o.partition) C).length=1)
 (refJ : VertexGeometry.Refines J o.partition) (aJ : A∈J) (cJ : C∈J)
 (agree : agreement T S F=true) (refF : VertexGeometry.Refines F o.partition)
 (badA : restrictionAgrees S T A=false) (goodC : restrictionAgrees S T C=true) (budget : F.length-1≤q)
 (knownRun : BothBad.knownOne T S A=some known)
 (monoB : ParentMono o.partition B (sideColor (PairGeometry.descendants T p)))
 (clearAB : PairGeometry.ActualClear T A B p)
 (clearAC : Clear (minimalVertices A T) (minimalVertices C T))
 (clearBC : Clear (minimalVertices B T) (minimalVertices C T)) :
 o.sourceCuts.length+1≤q ∧ q-o.sourceCuts.length-1<q ∧
 ∃H,BothBad.checked T S q (BothBad.dispatch (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) T S
  ⟨o,.retained A B C known,q-o.sourceCuts.length-1⟩).answer=some H ∧ agreement T S H=true ∧ H.length≤F.length := by
 obtain ⟨pay,strict,_,G,runG,agreeG,_,bound⟩:=retained_paid_B_call ordinary q T S A B C o below proper
  parents part emb refP payment oneA oneC F agree refF badA budget
 have glued:=retained_assemble T S A B C o.partition J p known G proper parents part emb refP refJ aJ cJ
  knownRun goodC agreeG monoB clearAB clearAC clearBC
 let H:=known++G++[C]
 have least : H.length≤F.length:=by
  dsimp only [H]
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega
 have hbudget : H.length-1≤q:=by omega
 refine ⟨pay,strict,H,?_,glued.1,least⟩
 dsimp only [H] at hbudget ⊢
 simp only [BothBad.dispatch,runG,Option.map_some,BothBad.checked,Option.bind_some,BothBad.accept,
  glued.1,decide_eq_true hbudget,Bool.and_self,ite_true]
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.literal_retained_dispatch_complete
#print axioms ContactedHard2Survival.literal_retained_dispatch_complete
