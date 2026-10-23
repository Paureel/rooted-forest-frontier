import AllGoodParents
import OrdinaryLocal
namespace OrdinaryDispatch.DisjointParents
open RMAF ForestState OutputState RestrictionBridge Universal233 Universal233.CherryBranching Universal233.BothBad
abbrev BelowIH (q : Nat) (actual : Ordinary) := ∀r,r<q→ForestMinCompletion.LocalOrdinaryIH r actual

theorem query_complete (actual : Ordinary) (T S : Tree) (P : OrdinaryDispatch.Forest) (q : Nat)
 (below : BelowIH q actual) (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (part : partitionCheck (leaves S) P=true)
 (es : pairwiseEmbeddings S P=true) (et : pairwiseEmbeddings T P=true)
 (positive : 1≤P.length-1)
 (F : OrdinaryDispatch.Forest) (hf : agreement T S F=true) (href : Refines F P) (budget : F.length-1≤q) :
 ∃G,(query actual T S P q).answer=some G ∧ G.length≤F.length := by
 have plen := refined_length part es hf href
 have affordable : P.length-1≤q := by omega
 have low : q-(P.length-1)<q := by omega
 have rb : F.length-P.length≤q-(P.length-1) := by omega
 obtain ⟨G,hG,ha,refG,bill,min⟩ := BothBadLocal.ordinary_candidate_local actual T S P (q-(P.length-1)) F
  ns nt part es et hf href rb (below _ low)
 refine ⟨G,?_,min⟩
 unfold query
 simp only [affordable,ite_true]
 rw [hG]
 exact checked_complete T S q G ha (by omega)

theorem query_minimum (actual : Ordinary) (T S : Tree) (P : OrdinaryDispatch.Forest) (q : Nat)
 (below : BelowIH q actual) (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (part : partitionCheck (leaves S) P=true)
 (es : pairwiseEmbeddings S P=true) (et : pairwiseEmbeddings T P=true)
 (positive : 1≤P.length-1)
 (G : OrdinaryDispatch.Forest) (answer : (query actual T S P q).answer=some G) :
 agreement T S G=true ∧ G.length-1≤q ∧
 ∀F,agreement T S F=true→Refines F P→G.length≤F.length := by
 have gs := query_sound actual T S P G q answer
 refine ⟨gs.1,gs.2,?_⟩
 intro F hf href
 by_cases budget : F.length-1≤q
 · obtain ⟨H,hH,min⟩ := query_complete actual T S P q below nt ns part es et positive F hf href budget
   have eq : H=G := Option.some.inj (hH.symm.trans answer)
   simpa [eq] using min
 · omega

theorem run_complete (actual : Ordinary) (T S : Tree) (a b q : Nat)
 {p : RMAF.Vertex} (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) (ch : CoreGraph.CherryAt T p a b)
 (two : (cuts S a b).length=2)
 (disjoint : pairwiseEmbeddings T (pendantPartition S a b)=true)
 (below : BelowIH q actual)
 (F : OrdinaryDispatch.Forest) (hf : agreement T S F=true) (budget : F.length-1≤q) :
 ∃G,run actual T S a b q=some G ∧ G.length≤F.length := by
 obtain ⟨part,es,paid⟩ := pendant_checks nt ns same ch
 apply run_complete_from_parent actual T S a b q nt ns same ch below
 · intro H ha href hb
   exact query_complete actual T S (pendantPartition S a b) q below nt ns part es disjoint
    (by have len:=partition_length S a b;omega) H ha href hb
 · exact hf
 · exact budget

theorem run_minimum (actual : Ordinary) (T S : Tree) (a b q : Nat)
 {p : RMAF.Vertex} (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) (ch : CoreGraph.CherryAt T p a b)
 (two : (cuts S a b).length=2)
 (disjoint : pairwiseEmbeddings T (pendantPartition S a b)=true)
 (below : BelowIH q actual)
 (G : OrdinaryDispatch.Forest) (answer : run actual T S a b q=some G) :
 agreement T S G=true ∧ G.length-1≤q ∧ ∀F,agreement T S F=true→G.length≤F.length := by
 have gs := run_sound actual T S a b q G answer
 refine ⟨gs.1,gs.2,?_⟩
 intro F hf
 by_cases budget : F.length-1≤q
 · obtain ⟨H,hH,min⟩ := run_complete actual T S a b q nt ns same ch two disjoint below F hf budget
   have eq : H=G := Option.some.inj (hH.symm.trans answer)
   simpa [eq] using min
 · omega
end OrdinaryDispatch.DisjointParents
