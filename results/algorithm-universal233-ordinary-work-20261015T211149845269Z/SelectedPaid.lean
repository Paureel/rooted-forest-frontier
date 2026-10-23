import FastHard2PaidPaidCaller
namespace Universal233.Hard2PaidLocal
open RMAF CoreProgram SourceCoverage VertexGeometry BothBad BothBadLocal PaidAssembly Hard2Overlap Integration

def Covers (actual : Ordinary) (T S : Tree) (q : Nat) (outs : List Output) (F : Forest) : Prop :=
 ∃H,(runOutputs actual T S q outs).answer=some H ∧ agreement T S H=true ∧
 H.length-1≤q ∧ H.length≤F.length

theorem selected_clique_cover {T S : Tree} {A B C : List Nat} {v : RMAF.Vertex} {F : Forest} {q : Nat}
 (actual : Ordinary) (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : select T A B C=some (.clique v)) (hf : agreement T S F=true)
 (hr : RefinesBlocks F [A,B,C]) (hq : F.length-1≤q) (IH : BelowIH q actual) :
 Covers actual T S q (outputs (.clique v) S T A B q) F := by
 have hl:=fun x hx=>(same x).1 hx
 obtain ⟨hi,_,_,_⟩ := select_sound ht hl hp selected
 obtain ⟨out,mem,witness,_⟩ := clique_list_cover T S A B C F v q ht hs hl hf hp hr hi hq
 exact runOutputs_cover actual T S q A B C (.clique v) [A,B,C] F hs ht same hp hf hq IH ⟨out,mem,witness⟩

theorem selected_four_cover {T S : Tree} {A B C : List Nat} {o : Order} {v w : RMAF.Vertex} {F : Forest} {q : Nat}
 (actual : Ordinary) (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : select T A B C=some (.four o v w)) (hf : agreement T S F=true)
 (hr : RefinesBlocks F [A,B,C]) (hq : F.length-1≤q) (IH : BelowIH q actual) :
 Covers actual T S q (outputs (.four v w) S T (first o A B C) (second o A B C) q) F := by
 have hl:=fun x hx=>(same x).1 hx
 obtain ⟨g,_⟩ := select_sound ht hl hp selected
 have pp:=permuted_partition o hp
 have rr:=refines_perm hr (parents_perm o A B C).symm
 obtain ⟨out,mem,witness,_⟩ := four_list_cover T S _ _ _ F v w q ht hs hl hf pp rr g.1 g.2.1 hq
 exact runOutputs_cover actual T S q _ _ (third o A B C) (.four v w) _ F hs ht same pp hf hq IH ⟨out,mem,witness⟩

theorem selected_diagonal_cover {T S : Tree} {A B C : List Nat} {o : Order} {v w : RMAF.Vertex} {F : Forest} {q : Nat}
 (actual : Ordinary) (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : select T A B C=some (.diagonal o v w)) (hf : agreement T S F=true)
 (hr : RefinesBlocks F [A,B,C]) (hq : F.length-1≤q) (IH : BelowIH q actual) :
 Covers actual T S q (outputs (.diagonal v w) S T (first o A B C) (second o A B C) q) F := by
 have hl:=fun x hx=>(same x).1 hx
 obtain ⟨g,count⟩ := select_sound ht hl hp selected
 have pp:=permuted_partition o hp
 have rr:=refines_perm hr (parents_perm o A B C).symm
 obtain ⟨out,mem,witness,_⟩ := diagonal_list_cover T S _ _ _ F v w q ht hs hl hf pp rr g.1 g.2.1
  g.2.2.2.1 g.2.2.2.2.1 count hq
 exact runOutputs_cover actual T S q _ _ (third o A B C) (.diagonal v w) _ F hs ht same pp hf hq IH ⟨out,mem,witness⟩

theorem selected_vertex_cover {T S : Tree} {A B C : List Nat} {o : Order} {v : RMAF.Vertex} {F : Forest} {q : Nat}
 (actual : Ordinary) (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : select T A B C=some (.pair o (.vertex v))) (hf : agreement T S F=true)
 (hr : RefinesBlocks F [A,B,C]) (hq : F.length-1≤q) (IH : BelowIH q actual) :
 Covers actual T S q (outputs (.vertex v) S T (first o A B C) (second o A B C) q) F := by
 have hl:=fun x hx=>(same x).1 hx
 obtain ⟨_,_,_,av,bv,_⟩ := select_sound ht hl hp selected
 have pp:=permuted_partition o hp
 have rr:=refines_perm hr (parents_perm o A B C).symm
 obtain ⟨out,mem,witness,_⟩ := PairAssembly.vertex_pair_cover T S _ _ _ F v q ht hs hl hf pp rr av bv hq
 exact runOutputs_cover actual T S q _ _ (third o A B C) (.vertex v) _ F hs ht same pp hf hq IH ⟨out,mem,witness⟩
end Universal233.Hard2PaidLocal
