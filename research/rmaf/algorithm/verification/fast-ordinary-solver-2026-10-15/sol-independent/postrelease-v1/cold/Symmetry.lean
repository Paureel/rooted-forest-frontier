import SelectedContinuation
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

theorem choose_swap (T : Tree) (A B : List Nat)
    (hp : PairGeometry.properInput T A B = true)
    (hq : PairGeometry.properInput T B A = true) :
    PairGeometry.choose T B A = PairGeometry.choose T A B := by
  have hv : PairGeometry.vertexOK T B A = PairGeometry.vertexOK T A B := by
    funext v
    simp only [PairGeometry.vertexOK,Bool.and_comm,Bool.and_left_comm,Bool.and_assoc,Bool.or_comm]
  have he : PairGeometry.edgeOK T B A = PairGeometry.edgeOK T A B := by
    funext e
    simp only [PairGeometry.edgeOK,Bool.and_comm,Bool.and_left_comm,Bool.and_assoc]
  simp only [PairGeometry.choose,hp,hq,ite_true,hv,he]

theorem embeddings_swap (S : Tree) (A B C : List Nat)
    (hp : pairwiseEmbeddings S [A,B,C] = true) : pairwiseEmbeddings S [B,A,C] = true := by
  have hs := (executable_pairwiseEmbeddings S [A,B,C]).1 hp
  have hab : Disj S A B := (List.pairwise_cons.1 hs).1 _ (by simp)
  have hac : Disj S A C := (List.pairwise_cons.1 hs).1 _ (by simp)
  have hbc : Disj S B C := (List.pairwise_cons.1 (List.pairwise_cons.1 hs).2).1 _ (by simp)
  apply (executable_pairwiseEmbeddings S _).2
  apply List.pairwise_cons.2
  constructor
  · intro L hL
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl
    · exact disj_symm hab
    · exact hbc
  · apply List.pairwise_cons.2
    constructor
    · intro L hL
      have he : L = C := by simpa using hL
      subst L
      exact hac
    · simp

/-- Exact symmetry uses the SAME selected original edge, not a newly assumed
B-side graph/rank hypothesis. Apply selected_cheap_continuation with swapped
parents via these kernel-proved source and selector equalities. -/
theorem selected_symmetry (S T : Tree) (A B C : List Nat)
    (e : RMAF.Vertex × RMAF.Vertex)
    (ht : (leaves T).Nodup) (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hsource : pairwiseEmbeddings S [A,B,C] = true)
    (hchoose : PairGeometry.choose T A B = some (.edge e)) :
    partitionCheck (leaves S) [B,A,C] = true ∧ pairwiseEmbeddings S [B,A,C] = true ∧
      PairGeometry.choose T B A = some (.edge e) := by
  have hswap := partition_swap _ A B C hp
  exact ⟨hswap,embeddings_swap S A B C hsource,
    (choose_swap T A B (proper_pair_from_partition S T A B C ht hl hp)
      (proper_pair_from_partition S T B A C ht hl hswap)).trans hchoose⟩
end Universal233.BinaryCheap
