import ActualHard2
namespace Universal233.Hard2Overlap
open RMAF CoreGraph CoreProgram Integration VertexGeometry SourceCoverage CutRealization HardParent PaidAssembly

theorem refines_perm {F P Q : List (List Nat)} (h : RefinesBlocks F P) (perm : P.Perm Q) : RefinesBlocks F Q := by
 intro K hK
 obtain ⟨B,hB,hKB⟩ := h K hK
 exact ⟨B,perm.mem_iff.1 hB,hKB⟩
theorem witness_perm {S : Tree} {P Q F : List (List Nat)} {q : Nat} {o : Output}
 (h : OutputWitness S P F q o) (perm : P.Perm Q) : OutputWitness S Q F q o :=
 ⟨h.1,refines_perm h.2.1 perm,h.2.2⟩

theorem four_mass_of_guards {T S : Tree} {A B C : List Nat} {v w : RMAF.Vertex}
 (ht : (leaves T).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (g : ChainGuards T A B C v w)
 (count : 3≤(jointColors B T v w).length) (q : Nat) (c : Rat) (base : 2≤c) :
 rawQMass c (WholeSourceMass.fourChainOutputs S T A B v w q)≤4*c^(-4 : Int) := by
 have call := partition_mass_interface S T A B C hp ht hl
 obtain ⟨ha,hb,hc⟩ := WholeSourceMass.partition_target_support S T A B C call.partition hl
 obtain ⟨hi,hj,av,bv,bw,cw,_,_⟩ := g
 exact WholeSourceMass.four_chain_raw_mass S T A B C call v w
  (occupied_of_internal T A v ha hi av) (occupied_of_internal T B v hb hi bv)
  (occupied_of_internal T B w hb hj bw) (occupied_of_internal T C w hc hj cw) count q c base
theorem diagonal_mass_of_guards {T S : Tree} {A B C : List Nat} {v w : RMAF.Vertex}
 (ht : (leaves T).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (g : ChainGuards T A B C v w)
 (count : (jointColors B T v w).length=2) (q : Nat) (c : Rat) (base : 2≤c) :
 rawQMass c (WholeSourceMass.diagonalOutputs S T A B v w q)≤c^(-3 : Int)+c^(-4 : Int) := by
 have call := partition_mass_interface S T A B C hp ht hl
 obtain ⟨ha,hb,hc⟩ := WholeSourceMass.partition_target_support S T A B C call.partition hl
 obtain ⟨hi,hj,av,bv,bw,cw,_,_⟩ := g
 exact WholeSourceMass.diagonal_raw_mass S T A B C call v w
  (occupied_of_internal T A v ha hi av) (occupied_of_internal T C w hc hj cw) count q c base

theorem actual_clique_paid {T S : Tree} {F : List (List Nat)} {v z p r : RMAF.Vertex} {a b q : Nat}
 (ht : (leaves T).Nodup) (hs : (leaves S).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hf : agreement T S F=true) (ch : CherryAt T z a b) (cuts : pendantOriginal S a b=[p,r])
 (selected : select T (leftParent S p) (rightParent S r) (rootParent S p r)=some (.clique v))
 (hq : F.length-1≤q) (c : Rat) (base : 2≤c) :
 Hard2Covered S F a b p r q (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q)
  (fun o=>CliqueClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v) ∧
 rawQMass c (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q)≤3*c^(-4 : Int) := by
 have hp := (hard2_refinement_split hs hf ch cuts).2.1
 obtain ⟨hi,av,bv,cv⟩ := select_sound ht hl hp selected
 exact hard2_clique_paid T S F v q ht hs hl hf ch cuts hi av bv cv hq c base

theorem actual_four_paid {T S : Tree} {F : List (List Nat)} {o : Order} {v w z p r : RMAF.Vertex} {a b q : Nat}
 (ht : (leaves T).Nodup) (hs : (leaves S).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hf : agreement T S F=true) (ch : CherryAt T z a b) (cuts : pendantOriginal S a b=[p,r])
 (selected : select T (leftParent S p) (rightParent S r) (rootParent S p r)=some (.four o v w))
 (hq : F.length-1≤q) (c : Rat) (base : 2≤c) :
 let A:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
 let B:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
 let C:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
 Hard2Covered S F a b p r q (WholeSourceMass.fourChainOutputs S T A B v w q)
  (fun out=>FourClearing T out.partition A B C v w) ∧
 rawQMass c (WholeSourceMass.fourChainOutputs S T A B v w q)≤4*c^(-4 : Int) := by
 obtain ⟨graph,hp,cases⟩ := hard2_refinement_split hs hf ch cuts
 obtain ⟨guards,count⟩ := select_sound ht hl hp selected
 have pp := permuted_partition o hp
 refine ⟨⟨graph,hp,?_⟩,four_mass_of_guards ht hl pp guards count q c base⟩
 rcases cases with ha|hb|hr
 · exact Or.inl ha
 · exact Or.inr (Or.inl hb)
 · have rr := refines_perm hr (parents_perm o _ _ _).symm
   obtain ⟨out,mem,hw,clear⟩ := four_list_cover T S _ _ _ F v w q ht hs hl hf pp rr guards.1 guards.2.1 hq
   exact Or.inr (Or.inr ⟨out,mem,witness_perm hw (parents_perm o _ _ _),clear⟩)

theorem actual_diagonal_paid {T S : Tree} {F : List (List Nat)} {o : Order} {v w z p r : RMAF.Vertex} {a b q : Nat}
 (ht : (leaves T).Nodup) (hs : (leaves S).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hf : agreement T S F=true) (ch : CherryAt T z a b) (cuts : pendantOriginal S a b=[p,r])
 (selected : select T (leftParent S p) (rightParent S r) (rootParent S p r)=some (.diagonal o v w))
 (hq : F.length-1≤q) (c : Rat) (base : 2≤c) :
 let A:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
 let B:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
 let C:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
 Hard2Covered S F a b p r q (WholeSourceMass.diagonalOutputs S T A B v w q)
  (fun out=>DiagonalClearing T out.partition A B C v w) ∧
 rawQMass c (WholeSourceMass.diagonalOutputs S T A B v w q)≤c^(-3 : Int)+c^(-4 : Int) := by
 obtain ⟨graph,hp,cases⟩ := hard2_refinement_split hs hf ch cuts
 obtain ⟨guards,count⟩ := select_sound ht hl hp selected
 have pp := permuted_partition o hp
 refine ⟨⟨graph,hp,?_⟩,diagonal_mass_of_guards ht hl pp guards count q c base⟩
 rcases cases with ha|hb|hr
 · exact Or.inl ha
 · exact Or.inr (Or.inl hb)
 · have rr := refines_perm hr (parents_perm o _ _ _).symm
   obtain ⟨out,mem,hw,clear⟩ := diagonal_list_cover T S _ _ _ F v w q ht hs hl hf pp rr
     guards.1 guards.2.1 guards.2.2.2.1 guards.2.2.2.2.1 count hq
   exact Or.inr (Or.inr ⟨out,mem,witness_perm hw (parents_perm o _ _ _),clear⟩)
end Universal233.Hard2Overlap
