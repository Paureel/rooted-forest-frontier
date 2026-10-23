import CoreCherry
import Count
import Equivalence
import CherryReplacement
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

/-- Literal generic source-edge split of every original agreement block. -/
def splitForest (F : List (List Nat)) (X : List Nat) :=
 BinaryExchange.splitAll F X.contains

theorem source_treeAt (S : Tree) (q : RMAF.Vertex) : BinaryExchange.treeAt S q = subtree S q := by
 induction q generalizing S with
 | nil => simp [BinaryExchange.treeAt,CoreGraph.subtree]
 | cons s q ih =>
   cases S with
   | leaf x => rfl
   | node l r => cases s <;> exact ih _

theorem source_subtree_labels {S U : Tree} {q : RMAF.Vertex}
 (h : subtree S q = some U) : subtreeLabels S q = leaves U := by
 induction q generalizing S with
 | nil => simp [subtree] at h; subst S; rfl
 | cons s q ih =>
   cases S with
   | leaf x => simp [subtree] at h
   | node l r => exact ih h

theorem split_original_agreement {T S U : Tree} {q : RMAF.Vertex} {F : List (List Nat)}
 (hn : (leaves S).Nodup) (hq : subtree S q = some U)
 (ha : agreement T S F = true) :
 agreement T S (splitForest F (leaves U)) = true ∧
 (splitForest F (leaves U)).length ≤ F.length+1 := by
 open BinaryExchange in
 have ht : treeAt S q = some U := by rw [source_treeAt]; exact hq
 open BinaryExchange in
 obtain ⟨hpT,hpS,top,embT,embS⟩ := agreement_parts T S F ha
 open BinaryExchange in
 have splitclear : ∀ B, B ∈ F → Disj T (yes B (leaves U).contains) (no B (leaves U).contains) ∧
     Disj S (yes B (leaves U).contains) (no B (leaves U).contains) := by
   intro B hB
   have hh := descendant_agreed_split T S U q B hn ht (top B hB)
   exact ⟨(executable_disjointVertices T _ _).1 hh.2.1,(executable_disjointVertices S _ _).1 hh.2.2⟩
 open BinaryExchange in
 have partition_split : ∀ L, partitionCheck L F = true →
     partitionCheck L (splitForest F (leaves U)) = true := by
   intro L hp
   obtain ⟨ne,counts,labs⟩ := partition_parts L F hp
   exact partition_intro L _ (splitAll_nonempty F _)
     (by intro x hx; change (splitAll F (leaves U).contains).flatten.count x = 1; rw [splitAll_count]; exact counts x hx)
     (by intro x hx; exact labs x ((splitAll_labels F _ x).1 hx))
 open BinaryExchange in
 have newtop : ∀ B, B ∈ splitForest F (leaves U) → restrictionAgrees T S B = true := by
   intro B hB
   obtain ⟨C,hC,hCB⟩ := List.mem_flatMap.1 hB
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (((mem_split C B _).1 hCB).2)
   exact restrictionAgrees_sub T S C B (top C hC) (split_sub C B _ hCB)
     ⟨x,hx,partition_sub (leaves T) F hpT C hC x (split_sub C B _ hCB x hx)⟩
 have newagree : agreement T S (splitForest F (leaves U)) = true := by
   simp only [agreement,Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings]
   exact ⟨⟨⟨⟨partition_split _ hpT,partition_split _ hpS⟩,newtop⟩,
     BinaryExchange.splitAll_pairwise T F _ embT (fun B hB => (splitclear B hB).1)⟩,
     BinaryExchange.splitAll_pairwise S F _ embS (fun B hB => (splitclear B hB).2)⟩
 have count := BinaryExchange.mixed_blocks_at_most_one S U q F hn ht embS
   (fun B hB => BinaryExchange.partition_sub _ _ hpS B hB)
 have count' : (F.filter (BinaryExchange.mixed · (leaves U).contains)).length ≤ 1 := count
 clear count
 have length := BinaryExchange.splitAll_length F (leaves U).contains
 exact ⟨newagree,by dsimp [splitForest]; omega⟩

theorem one_partition {S : Tree} {a b : Nat} {q : RMAF.Vertex}
 (hq : cuts S a b = [q]) : pendantPartition S a b =
 [subtreeLabels S q,(leaves S).filter (fun x => !(subtreeLabels S q).contains x)] := by
 simp [pendantPartition,coreLabels,hq]

theorem split_refines_one {T S : Tree} {F : List (List Nat)}
 (ha : agreement T S F = true) {a b : Nat} {q : RMAF.Vertex}
 (hq : cuts S a b = [q]) :
 Refines (splitForest F (subtreeLabels S q)) (pendantPartition S a b) := by
 intro B hB
 obtain ⟨C,hC,hCB⟩ := List.mem_flatMap.1 hB
 rcases BinaryExchange.split_mono C (subtreeLabels S q).contains B hCB with hy | hn
 · refine ⟨subtreeLabels S q,by simp [one_partition hq],?_⟩
   intro x hx; exact List.contains_iff_mem.1 (hy x hx)
 · refine ⟨(leaves S).filter (fun x => !(subtreeLabels S q).contains x),by simp [one_partition hq],?_⟩
   intro x hx
   have labs := block_labels (source_agreement_checks ha).1 hC (BinaryExchange.split_sub C B _ hCB x hx)
   have hxnot : x ∉ subtreeLabels S q := by simpa using hn x hx
   simp [labs,hxnot]

theorem split_endpoint_survives {F : List (List Nat)} {a : Nat} (X : List Nat)
 (hs : [a] ∈ F) (ha : a ∉ X) : [a] ∈ splitForest F X := by
 apply List.mem_flatMap.2
 refine ⟨[a],hs,?_⟩
 simp [BinaryExchange.split,BinaryExchange.yes,BinaryExchange.no,ha]
end Universal233.CherryBranching
