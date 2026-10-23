import LiteralControls
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer
abbrev cheapColor (A B D : List Nat) : Nat → Nat := WholeSourceMass.taggedColor B A (fun _ => 0) (sideColor D) (fun _ => 0)
def ay (A D : List Nat) := yes A (D.contains ·)
def an (A D : List Nat) := no A (D.contains ·)

theorem partition_swap (L : List Nat) (A B C : List Nat)
    (hp : partitionCheck L [A,B,C] = true) : partitionCheck L [B,A,C] = true := by
  have hf : ([A,B,C] : List (List Nat)).Perm [B,A,C] := (List.Perm.swap A B [C]).symm
  have hflat := hf.flatten
  simp only [partitionCheck] at hp ⊢
  rw [←hf.all_eq,←hflat.all_eq]
  have hc : (fun x => ([B,A,C] : List (List Nat)).flatten.count x == 1) =
      (fun x => ([A,B,C] : List (List Nat)).flatten.count x == 1) := by
    funext x; rw [hflat.count_eq x]
  rw [hc]
  exact hp

/-- The actual selected binary edge supplies nonempty sectors and all four
mutual-clear facts. Sector separation is proved from its original subtree. -/
theorem edge_facts (T : Tree) (A B : List Nat) (e : RMAF.Vertex × RMAF.Vertex)
    (hchoose : PairGeometry.choose T A B = some (.edge e)) :
    ∃ u, treeAt T e.2 = some u ∧
      ay A (leaves u) ≠ [] ∧ an A (leaves u) ≠ [] ∧
      ay B (leaves u) ≠ [] ∧ an B (leaves u) ≠ [] ∧
      Disj T (ay A (leaves u)) B ∧ Disj T (an A (leaves u)) B ∧
      Disj T (ay B (leaves u)) A ∧ Disj T (an B (leaves u)) A ∧
      Disj T (ay A (leaves u)) (an A (leaves u)) ∧
      Disj T (ay B (leaves u)) (an B (leaves u)) := by
  obtain ⟨hp,hvalid⟩ := PairGeometry.choose_sound T A B (.edge e) hchoose
  have ht := PairGeometry.proper_nodup T A B hp
  obtain ⟨he,hap,hbp,hav,hbv,has,hbs,hclear⟩ := hvalid
  obtain ⟨u,hu⟩ := FreshPairReview.original_vertex_treeAt T e.2 (PairGeometry.minimal_vertices A T e.2 hav)
  have hay : ay A (leaves u) ≠ [] := by rw [ay,←FreshPairReview.side_yes A T u e.2 ht hu]; exact has true
  have han : an A (leaves u) ≠ [] := by rw [an,←FreshPairReview.side_no A T u e.2 ht hu]; exact has false
  have hby : ay B (leaves u) ≠ [] := by rw [ay,←FreshPairReview.side_yes B T u e.2 ht hu]; exact hbs true
  have hbn : an B (leaves u) ≠ [] := by rw [an,←FreshPairReview.side_no B T u e.2 ht hu]; exact hbs false
  have cay : Disj T (ay A (leaves u)) B := by rw [ay,←FreshPairReview.side_yes A T u e.2 ht hu]; exact FreshPairReview.actual_clear_disj T _ _ (hclear.1 true)
  have can : Disj T (an A (leaves u)) B := by rw [an,←FreshPairReview.side_no A T u e.2 ht hu]; exact FreshPairReview.actual_clear_disj T _ _ (hclear.1 false)
  have cby : Disj T (ay B (leaves u)) A := by rw [ay,←FreshPairReview.side_yes B T u e.2 ht hu]; exact FreshPairReview.actual_clear_disj T _ _ (hclear.2 true)
  have cbn : Disj T (an B (leaves u)) A := by rw [an,←FreshPairReview.side_no B T u e.2 ht hu]; exact FreshPairReview.actual_clear_disj T _ _ (hclear.2 false)
  have hcluster := subtree_cluster T u e.2 ht hu
  have ca : Cluster (fun x => x ∈ A) ((leaves u).contains ·) T := cluster_weaken hcluster (by intros; trivial)
  have cb : Cluster (fun x => x ∈ B) ((leaves u).contains ·) T := cluster_weaken hcluster (by intros; trivial)
  exact ⟨u,hu,hay,han,hby,hbn,cay,can,cby,cbn,
    (executable_disjointVertices T _ _).1 (cluster_disjoint A _ T ca),
    (executable_disjointVertices T _ _).1 (cluster_disjoint B _ T cb)⟩

theorem cheap_rank (S T : Tree) (A B C D : List Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (ht : (leaves T).Nodup) (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hy : ay A D ≠ []) (hn : an A D ≠ []) : inputRank S (cheapColor A B D) = 4 :=
  side_input_color_count S T B A C D (partition_swap _ A B C hp) ht hl hy hn

/-- Literal q3 acceptance binds the very same generated output and original
source validity to the exact FULL original input color classes. -/
theorem accepted_cheap (S T : Tree) (A B C D : List Nat)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hy : ay A D ≠ []) (hn : an A D ≠ [])
    (haccept : fourAccepted S (cheapColor A B D) = true) :
    ∃ o, sideOutputs S B A D 3 = [o] ∧ o.sourceCuts.length = 3 ∧
      partitionCheck (leaves S) o.partition = true ∧ pairwiseEmbeddings S o.partition = true ∧
      o.partition.length = 4 ∧
      (∀ K, K ∈ o.partition → ∀ y, y ∈ K ↔ y ∈ leaves S ∧ cheapColor A B D y = cheapColor A B D (K.headD 0)) ∧
      (∀ q, 3 ≤ q → sideOutputs S B A D q = [o]) := by
  have hr := cheap_rank S T A B C D hp ht hl hy hn
  have hf := (four_accepted_iff S (cheapColor A B D) hs hr).1 haccept
  obtain ⟨o,ho,hcost,hclasses⟩ := feasible_unique_color_classes S _ hs hf 3 (by rw [hr]; decide)
  have hm : o ∈ (generate S (cheapColor A B D) 3).outputs := by rw [ho]; simp
  have hv := Assembly.generated_source_valid S _ 3 o hm
  have hlen := generate_partition_cost S _ 3 o hm
  refine ⟨o,ho,by simpa [hr] using hcost,hv.1,hv.2,by omega,hclasses,?_⟩
  intro q hq
  obtain ⟨z,hz,hzcost⟩ := feasible_unique S _ hs hf q (by rw [hr]; omega)
  have hmem := generate_outputs_mono S (cheapColor A B D) hq o hm
  have he : o = z := by simpa [hz] using hmem
  change (generate S (cheapColor A B D) q).outputs = [o]
  simpa [he] using hz
end Universal233.BinaryCheap

axiom source_pin_plant : False
