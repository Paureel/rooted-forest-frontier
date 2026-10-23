import SelectedEdge
namespace Universal233.Hard2PaidLocal
open RMAF CoreProgram SourceCoverage VertexGeometry BothBad BothBadLocal PaidAssembly Hard2Overlap Integration

def caseOutputs (S T : Tree) (A B C : List Nat) (q : Nat) : Result → List Output
 | .disjoint => []
 | .clique v => outputs (.clique v) S T A B q
 | .four o v w => outputs (.four v w) S T (first o A B C) (second o A B C) q
 | .diagonal o v w => outputs (.diagonal v w) S T (first o A B C) (second o A B C) q
 | .pair o (.vertex v) => outputs (.vertex v) S T (first o A B C) (second o A B C) q
 | .pair o (.edge e) => edgeOutputs S T (first o A B C) (second o A B C) e q

def PaidCase (S T : Tree) (A B C : List Nat) : Result → Prop
 | .disjoint => False
 | .pair o (.edge _) => restrictionAgrees S T (first o A B C)=true ∨ restrictionAgrees S T (second o A B C)=true
 | _ => True

def caseMass (c : Rat) : Result → Rat
 | .disjoint => 0
 | .clique _ => 3*c^(-4 : Int)
 | .four _ _ _ => 4*c^(-4 : Int)
 | .diagonal _ _ _ => c^(-3 : Int)+c^(-4 : Int)
 | .pair _ (.vertex _) => c^(-3 : Int)+c^(-4 : Int)
 | .pair _ (.edge _) => c^(-3 : Int)

theorem selected_case_cover {T S : Tree} {A B C : List Nat} {out : Result} {F : Forest} {q : Nat}
 (actual : Ordinary) (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (source : pairwiseEmbeddings S [A,B,C]=true) (selected : select T A B C=some out)
 (enabled : PaidCase S T A B C out) (hf : agreement T S F=true)
 (hr : RefinesBlocks F [A,B,C]) (hq : F.length-1≤q) (IH : BelowIH q actual) :
 Covers actual T S q (caseOutputs S T A B C q out) F := by
 cases out with
 | disjoint => exact False.elim enabled
 | clique v => exact selected_clique_cover actual ht hs same hp selected hf hr hq IH
 | four o v w => exact selected_four_cover actual ht hs same hp selected hf hr hq IH
 | diagonal o v w => exact selected_diagonal_cover actual ht hs same hp selected hf hr hq IH
 | pair o choice =>
  cases choice with
  | vertex v => exact selected_vertex_cover actual ht hs same hp selected hf hr hq IH
  | edge e => exact selected_edge_cover actual ht hs same hp source selected enabled hf hr hq IH

theorem selected_case_raw_mass {T S : Tree} {A B C : List Nat} {out : Result}
 (ht : (leaves T).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (selected : select T A B C=some out)
 (q : Nat) (c : Rat) (base : 2≤c) :
 rawQMass c (caseOutputs S T A B C q out)≤caseMass c out := by
 have valid:=select_sound ht hl hp selected
 cases out with
 | disjoint => simp [caseOutputs,rawQMass,caseMass]
 | clique v =>
  obtain ⟨hi,av,bv,cv⟩:=valid
  have call:=partition_mass_interface S T A B C hp ht hl
  obtain ⟨ha,hb,hc⟩:=WholeSourceMass.partition_target_support S T A B C call.partition hl
  exact WholeSourceMass.clique_raw_mass S T A B C call v (occupied_of_internal T A v ha hi av)
   (occupied_of_internal T B v hb hi bv) (occupied_of_internal T C v hc hi cv) q c base
 | four o v w => exact four_mass_of_guards ht hl (permuted_partition o hp) valid.1 valid.2 q c base
 | diagonal o v w => exact diagonal_mass_of_guards ht hl (permuted_partition o hp) valid.1 valid.2 q c base
 | pair o choice =>
  have pp:=permuted_partition o hp
  cases choice with
  | vertex v =>
   obtain ⟨_,_,_,av,bv,three⟩:=valid
   exact PairAssembly.vertex_pair_three_mass S T _ _ _ v ht hl pp av bv three q c base
  | edge e =>
   obtain ⟨_,_,choose,_⟩:=valid
   change rawQMass c (edgeOutputs S T _ _ e q)≤_
   by_cases good : restrictionAgrees S T (first o A B C)=true
   · simp only [edgeOutputs,good,ite_true]
     exact edge_raw_mass ht hl pp choose q c base
   · simp only [edgeOutputs,good,ite_false]
     have pp':=BinaryCheap.partition_swap _ _ _ _ pp
     have proper:=PairAssembly.proper_pair_from_partition S T _ _ _ ht hl pp
     have proper':=PairAssembly.proper_pair_from_partition S T _ _ _ ht hl pp'
     have choose' : PairGeometry.choose T (second o A B C) (first o A B C)=some (.edge e) := by
      rw [BinaryCheap.choose_swap T _ _ proper proper']; exact choose
     exact edge_raw_mass ht hl pp' choose' q c base

theorem selected_case_calls_strict {T S : Tree} {A B C : List Nat} (out : Result)
 (actual : Ordinary) (q : Nat) (hs : (leaves S).Nodup) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (call : Call) (mem : call∈(runOutputs actual T S q (caseOutputs S T A B C q out)).calls) :
 call.budget+2≤q ∧ call.budget<q := by
 cases out with
 | disjoint => simpa [caseOutputs,runOutputs,entries,execute] using mem
 | clique v => exact runOutputs_family_calls_strict actual T S q A B C (.clique v) hs hp call mem
 | four o v w => exact runOutputs_family_calls_strict actual T S q _ _ (third o A B C) (.four v w) hs (permuted_partition o hp) call mem
 | diagonal o v w => exact runOutputs_family_calls_strict actual T S q _ _ (third o A B C) (.diagonal v w) hs (permuted_partition o hp) call mem
 | pair o choice =>
  have pp:=permuted_partition o hp
  cases choice with
  | vertex v => exact runOutputs_family_calls_strict actual T S q _ _ (third o A B C) (.vertex v) hs pp call mem
  | edge e =>
   change call∈(runOutputs actual T S q (edgeOutputs S T _ _ e q)).calls at mem
   by_cases good : restrictionAgrees S T (first o A B C)=true
   · simp only [edgeOutputs,good,ite_true] at mem
     exact runOutputs_family_calls_strict actual T S q _ _ (third o A B C) (.side _) hs pp call mem
   · simp only [edgeOutputs,good,ite_false] at mem
     exact runOutputs_family_calls_strict actual T S q _ _ (third o A B C) (.side _) hs (BinaryCheap.partition_swap _ _ _ _ pp) call mem
end Universal233.Hard2PaidLocal
