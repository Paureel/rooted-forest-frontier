import ColorMonochrome
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem agreement_source_partition (T S : Tree) (F : List (List Nat)) (agree : agreement T S F=true) :
 partitionCheck (leaves S) F=true := by
 have a:=agree;simp only [agreement,Bool.and_eq_true] at a;exact a.1.1.1.2

theorem agreement_source_embedding (T S : Tree) (F : List (List Nat)) (agree : agreement T S F=true) :
 pairwiseEmbeddings S F=true := by
 have a:=agree;simp only [agreement,Bool.and_eq_true] at a;exact a.2

theorem whole_source_cover (T S : Tree) (A B C : List Nat) (q : Nat) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q)
 (ca cb cc : Nat→Nat) (ma : ParentMono F A ca) (mb : ParentMono F B cb) (mc : ParentMono F C cc) :
 ∃o,o∈wholeOutputs S A B ca cb cc q ∧ VertexGeometry.Refines F o.partition ∧ CutRealization.RealizedOutput S o := by
 have apart:=partition_parent_apart _ _ _ _ part
 obtain ⟨o,mem,refine,real⟩:=CutRealization.generate_refinement_coverage S F (taggedColor A B ca cb cc)
  (IndependentReconstruction.proper_parts proper).2.1 (agreement_source_partition T S F agree)
  (agreement_source_embedding T S F agree) (tagged_monochrome F A B C ca cb cc ref apart.1 apart.2.1 apart.2.2 ma mb mc) q budget
 exact ⟨o,mem,refine,real⟩

theorem clique_source_cover (T S : Tree) (A B C : List Nat) (q : Nat) (F : List (List Nat)) (v : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q)
 (nonlabel : ¬selectedLeaves (leaves T) T v) :
 ∃o,o∈cliqueOutputs S T A B v q ∧ VertexGeometry.Refines F o.partition ∧ CutRealization.RealizedOutput S o := by
 have apart:=partition_parent_apart _ _ _ _ part
 have avoid:=three_parent_avoidance T F A B C v (agreement_nonempty T S F agree)
  (agreement_target_embedding T S F agree) apart.1 apart.2.1 apart.2.2
 rcases avoid with h|h|h
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (fun _=>0) (colorLabel T v) (colorLabel T v) (constant_monochrome F A)
    (avoidance_monochrome T S F B v proper agree nonlabel h.1) (avoidance_monochrome T S F C v proper agree nonlabel h.2)
   exact ⟨o,by simp only [cliqueOutputs,List.mem_append];exact Or.inl (Or.inl mem),refine,real⟩
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (colorLabel T v) (fun _=>0) (colorLabel T v) (avoidance_monochrome T S F A v proper agree nonlabel h.1)
    (constant_monochrome F B) (avoidance_monochrome T S F C v proper agree nonlabel h.2)
   exact ⟨o,by simp only [cliqueOutputs,List.mem_append];exact Or.inl (Or.inr mem),refine,real⟩
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (colorLabel T v) (colorLabel T v) (fun _=>0) (avoidance_monochrome T S F A v proper agree nonlabel h.1)
    (avoidance_monochrome T S F B v proper agree nonlabel h.2) (constant_monochrome F C)
   exact ⟨o,by simp only [cliqueOutputs,List.mem_append];exact Or.inr mem,refine,real⟩

theorem four_source_cover (T S : Tree) (A B C : List Nat) (q : Nat) (F : List (List Nat)) (v w : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q)
 (vn : ¬selectedLeaves (leaves T) T v) (wn : ¬selectedLeaves (leaves T) T w) :
 ∃o,o∈fourChainOutputs S T A B v w q ∧ VertexGeometry.Refines F o.partition ∧ CutRealization.RealizedOutput S o := by
 have apart:=partition_parent_apart _ _ _ _ part
 have avoid:=four_parent_avoidance T F A B C v w (agreement_nonempty T S F agree)
  (agreement_target_embedding T S F agree) apart.1 apart.2.2
 rcases avoid with h|h|h|h
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (fun _=>0) (colorLabel T v) (colorLabel T w) (constant_monochrome F A)
    (avoidance_monochrome T S F B v proper agree vn h.1) (avoidance_monochrome T S F C w proper agree wn h.2)
   exact ⟨o,by simp only [fourChainOutputs,List.mem_append];exact Or.inl (Or.inl (Or.inl mem)),refine,real⟩
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (fun _=>0) (jointLabel T v w) (fun _=>0) (constant_monochrome F A)
    (joint_monochrome T F B v w (avoidance_monochrome T S F B v proper agree vn h.1)
      (avoidance_monochrome T S F B w proper agree wn h.2)) (constant_monochrome F C)
   exact ⟨o,by simp only [fourChainOutputs,List.mem_append];exact Or.inl (Or.inl (Or.inr mem)),refine,real⟩
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (colorLabel T v) (fun _=>0) (colorLabel T w) (avoidance_monochrome T S F A v proper agree vn h.1)
    (constant_monochrome F B) (avoidance_monochrome T S F C w proper agree wn h.2)
   exact ⟨o,by simp only [fourChainOutputs,List.mem_append];exact Or.inl (Or.inr mem),refine,real⟩
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (colorLabel T v) (colorLabel T w) (fun _=>0) (avoidance_monochrome T S F A v proper agree vn h.1)
    (avoidance_monochrome T S F B w proper agree wn h.2) (constant_monochrome F C)
   exact ⟨o,by simp only [fourChainOutputs,List.mem_append];exact Or.inr mem,refine,real⟩

theorem vertex_source_cover (T S : Tree) (A B C : List Nat) (q : Nat) (F : List (List Nat)) (v : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q)
 (nonlabel : ¬selectedLeaves (leaves T) T v) :
 ∃o,o∈vertexPairOutputs S T A B v q ∧ VertexGeometry.Refines F o.partition ∧ CutRealization.RealizedOutput S o := by
 have apart:=partition_parent_apart _ _ _ _ part
 have avoid:=two_parent_avoidance T F A B v (agreement_nonempty T S F agree)
  (agreement_target_embedding T S F agree) apart.1
 rcases avoid with h|h
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (colorLabel T v) (fun _=>0) (fun _=>0) (avoidance_monochrome T S F A v proper agree nonlabel h)
    (constant_monochrome F B) (constant_monochrome F C)
   exact ⟨o,by simp only [vertexPairOutputs,List.mem_append];exact Or.inl mem,refine,real⟩
 · obtain ⟨o,mem,refine,real⟩:=whole_source_cover T S A B C q F proper part agree ref budget
    (fun _=>0) (colorLabel T v) (fun _=>0) (constant_monochrome F A)
    (avoidance_monochrome T S F B v proper agree nonlabel h) (constant_monochrome F C)
   exact ⟨o,by simp only [vertexPairOutputs,List.mem_append];exact Or.inr mem,refine,real⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.agreement_source_partition
#print axioms ContactedHard2Survival.agreement_source_partition
#check @ContactedHard2Survival.agreement_source_embedding
#print axioms ContactedHard2Survival.agreement_source_embedding
#check @ContactedHard2Survival.whole_source_cover
#print axioms ContactedHard2Survival.whole_source_cover
#check @ContactedHard2Survival.clique_source_cover
#print axioms ContactedHard2Survival.clique_source_cover
#check @ContactedHard2Survival.four_source_cover
#print axioms ContactedHard2Survival.four_source_cover
#check @ContactedHard2Survival.vertex_source_cover
#print axioms ContactedHard2Survival.vertex_source_cover
