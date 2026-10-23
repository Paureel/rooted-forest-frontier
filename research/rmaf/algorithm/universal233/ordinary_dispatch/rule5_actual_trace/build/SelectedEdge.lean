import SelectedPaid
import GoodPair
import Symmetry
namespace Universal233.Hard2PaidLocal
open RMAF CoreProgram SourceCoverage VertexGeometry BothBad BothBadLocal PaidAssembly Hard2Overlap Integration BinaryExchange

/-- The exchange witness is used only in this proof; runtime makes the literal side-colored call. -/
theorem edge_good_cover {T S : Tree} {A B C : List Nat} {e : RMAF.Vertex × RMAF.Vertex} {F : Forest} {q : Nat}
 (actual : Ordinary) (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (source : pairwiseEmbeddings S [A,B,C]=true) (ne : A≠B)
 (choose : PairGeometry.choose T A B=some (.edge e))
 (clear : ∀E,E∈[A,B,C] → E≠A → E≠B → Disj T E A ∧ Disj T E B)
 (good : restrictionAgrees S T A=true) (hf : agreement T S F=true)
 (hr : RefinesBlocks F [A,B,C]) (hq : F.length-1≤q) (IH : BelowIH q actual) :
 Covers actual T S q (outputs (.side (PairGeometry.descendants T e.2)) S T A B q) F := by
 obtain ⟨u,F',out,hu,_,af,ref,len,mem,witness,_⟩ :=
  PairAssembly.selected_edge_good_parent_core S T A B C e F q hs same hp source ne choose clear good
   (PairAssembly.agreement_swap T S F hf) hr hq 2 (by decide)
 have eq:=PairAssembly.side_outputs_descendant S T u A B e.2 ht hu q
 have cost : F'.length-1≤q:=Nat.le_trans (Nat.sub_le_sub_right len 1) hq
 have cover : ∃out,out∈outputs (.side (PairGeometry.descendants T e.2)) S T A B q ∧ OutputWitness S [A,B,C] F' q out :=
  ⟨out,by simpa only [outputs,eq] using mem,witness⟩
 obtain ⟨H,answer,agree,budget,length⟩ := runOutputs_cover actual T S q A B C (.side (PairGeometry.descendants T e.2))
  [A,B,C] F' hs ht same hp (PairAssembly.agreement_swap S T F' af) cost IH cover
 exact ⟨H,answer,agree,budget,Nat.le_trans length len⟩

def edgeOutputs (S T : Tree) (A B : List Nat) (e : RMAF.Vertex × RMAF.Vertex) (q : Nat) : List Output :=
 if restrictionAgrees S T A then outputs (.side (PairGeometry.descendants T e.2)) S T A B q
 else outputs (.side (PairGeometry.descendants T e.2)) S T B A q

theorem selected_edge_cover {T S : Tree} {A B C : List Nat} {o : Order} {e : RMAF.Vertex × RMAF.Vertex} {F : Forest} {q : Nat}
 (actual : Ordinary) (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
 (same : ∀x,x∈leaves S ↔ x∈leaves T) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (source : pairwiseEmbeddings S [A,B,C]=true)
 (selected : select T A B C=some (.pair o (.edge e)))
 (good : restrictionAgrees S T (first o A B C)=true ∨ restrictionAgrees S T (second o A B C)=true)
 (hf : agreement T S F=true) (hr : RefinesBlocks F [A,B,C]) (hq : F.length-1≤q) (IH : BelowIH q actual) :
 Covers actual T S q (edgeOutputs S T (first o A B C) (second o A B C) e q) F := by
 have hl:=fun x hx=>(same x).1 hx
 obtain ⟨pp,pe,ne,proper,choose,_,clear⟩ := selected_pair_guards ht hl hp source selected
 have rr:=refines_perm hr (parents_perm o A B C).symm
 by_cases ga : restrictionAgrees S T (first o A B C)=true
 · simp only [edgeOutputs,ga,ite_true]
   exact edge_good_cover actual ht hs same pp pe ne choose clear ga hf rr hq IH
 · have gb : restrictionAgrees S T (second o A B C)=true := good.resolve_left ga
   simp only [edgeOutputs,ga,ite_false]
   have pp':=BinaryCheap.partition_swap _ _ _ _ pp
   have pe':=BinaryCheap.embeddings_swap S _ _ _ pe
   have proper':=PairAssembly.proper_pair_from_partition S T _ _ _ ht hl pp'
   have choose' : PairGeometry.choose T (second o A B C) (first o A B C)=some (.edge e) := by
    rw [BinaryCheap.choose_swap T _ _ proper proper']; exact choose
   have rr':=refines_perm rr (List.Perm.swap _ _ _)
   have clear' : ∀E,E∈[second o A B C,first o A B C,third o A B C] → E≠second o A B C → E≠first o A B C →
    Disj T E (second o A B C) ∧ Disj T E (first o A B C) := by
    intro E mem nb na
    have mem' : E∈[first o A B C,second o A B C,third o A B C] := by simpa [or_comm,or_left_comm] using mem
    exact (clear E mem' na nb).symm
   exact edge_good_cover actual ht hs same pp' pe' (Ne.symm ne) choose' clear' gb hf rr' hq IH

/-- The sharp side-family mass follows from the actual selected edge, without F or a good-parent oracle. -/
theorem edge_raw_mass {T S : Tree} {A B C : List Nat} {e : RMAF.Vertex × RMAF.Vertex}
 (ht : (leaves T).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (choose : PairGeometry.choose T A B=some (.edge e))
 (q : Nat) (c : Rat) (base : 2≤c) :
 rawQMass c (outputs (.side (PairGeometry.descendants T e.2)) S T A B q)≤c^(-3 : Int) := by
 obtain ⟨u,hu,_,_,hy,hn,_⟩:=BinaryCheap.edge_facts T A B e choose
 have eq:=PairAssembly.side_outputs_descendant S T u A B e.2 ht hu q
 simpa only [outputs,eq] using PairAssembly.side_raw_mass S T A B C (leaves u) hp ht hl hy hn q c base
end Universal233.Hard2PaidLocal
