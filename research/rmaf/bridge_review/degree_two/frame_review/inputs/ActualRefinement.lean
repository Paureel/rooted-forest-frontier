import DegreeCounting
import AgreementBlock
import ActualSupportTransport

/-! Composition using the actual extractor, original restriction agreement,
and original agreement-partition predicate. No transport premise is assumed. -/
namespace DegreeTwo
open RMAF BridgeReview LeastEmbedding DegreeTwoGraph RestrictionRoute

/-- The target's full local refinement. Only the cut tree needs unique labels;
the stronger assumptions in the pin therefore also suffice. No equality of
the two full label sets is required. -/
theorem actual_two_tree_split (t u : Tree) (B : List Nat) (v : Vertex)
    (hnt : (leaves t).Nodup) (hB : B.Nodup)
    (hBt : ∀ x, x ∈ B → x ∈ leaves t)
    (hagree : restrictionAgrees t u B = true)
    (hdegree : actualDegree t B v = 2) :
    ∃ b0 b1 : List Nat,
      b0 ≠ [] ∧ b1 ≠ [] ∧ b0.Nodup ∧ b1.Nodup ∧
      (b0 ++ b1).Perm B ∧ (∀ x, x ∈ b0 → x ∉ b1) ∧
      restrictionAgrees t u b0 = true ∧ restrictionAgrees t u b1 = true ∧
      EmbSub t b0 B ∧ EmbSub t b1 B ∧ EmbSub u b0 B ∧ EmbSub u b1 B ∧
      disjointVertices (minimalVertices b0 t) (minimalVertices b1 t) = true ∧
      disjointVertices (minimalVertices b0 u) (minimalVertices b1 u) = true ∧
      v ∉ minimalVertices b0 t ∧ v ∉ minimalVertices b1 t := by
  obtain ⟨hv,hd⟩ := (actualDegree_two_iff t B v).mp hdegree
  obtain ⟨b0,b1,h0,h1,hn0,hn1,hp,hlabels,ht0,ht1,hdt,hv0,hv1⟩ :=
    actual_one_tree_split t B v hnt hB hv hd
  have h0B : ∀ x, x ∈ b0 → x ∈ B := by
    intro x hx
    exact hp.mem_iff.mp (List.mem_append_left b1 hx)
  have h1B : ∀ x, x ∈ b1 → x ∈ B := by
    intro x hx
    exact hp.mem_iff.mp (List.mem_append_right b0 hx)
  have ha0 := restrictionAgrees_subset t u b0 B h0B (fun x hx => hBt x (h0B x hx)) h0 hagree
  have ha1 := restrictionAgrees_subset t u b1 B h1B (fun x hx => hBt x (h1B x hx)) h1 hagree
  exact ⟨b0,b1,h0,h1,hn0,hn1,hp,hlabels,ha0,ha1,ht0,ht1,
    actual_support_mono b0 B u h0B, actual_support_mono b1 B u h1B,
    hdt,actual_disjoint_transport t u b0 b1 B h0B h1B hagree hdt,hv0,hv1⟩

/-- Replace the occupied piece anywhere in an actual agreement partition.
All old marks are predicates in their own tree's coordinates. -/
theorem actual_partition_split (t u : Tree) (before after : List (List Nat))
    (B : List Nat) (v : Vertex) (mt mu : Vertex → Prop)
    (hnt : (leaves t).Nodup)
    (h : agreement t u (before ++ B :: after) = true)
    (hmt : AvoidsPartition t (before ++ B :: after) mt)
    (hmu : AvoidsPartition u (before ++ B :: after) mu)
    (hdegree : actualDegree t B v = 2) :
    ∃ b0 b1 : List Nat, b0 ≠ [] ∧ b1 ≠ [] ∧ (b0 ++ b1).Perm B ∧
      agreement t u (before ++ b0 :: b1 :: after) = true ∧
      ¬ Occupied t (before ++ b0 :: b1 :: after) v ∧
      AvoidsPartition t (before ++ b0 :: b1 :: after) mt ∧
      AvoidsPartition u (before ++ b0 :: b1 :: after) mu ∧
      (before ++ b0 :: b1 :: after).length = (before ++ B :: after).length + 1 ∧
      (before ++ b0 :: b1 :: after).length - 1 =
        ((before ++ B :: after).length - 1) + 1 := by
  obtain ⟨_,hnB,hBt,_,ha⟩ := agreement_block t u before after B h
  obtain ⟨b0,b1,h0,h1,_,_,hp,_,ha0,ha1,ht0,ht1,hu0,hu1,hdt,hdu,hv0,hv1⟩ :=
    actual_two_tree_split t u B v hnt hnB hBt ha hdegree
  obtain ⟨hag,hclear,hmt',hmu',hcount⟩ := agreement_replace_and_clear
    t u before after B b0 b1 v mt mu h hmt hmu h0 h1 hp ha0 ha1
    ht0 ht1 hu0 hu1 hdt hdu ((actualDegree_two_iff t B v).mp hdegree).1 hv0 hv1
  exact ⟨b0,b1,h0,h1,hp,hag,hclear,hmt',hmu',hcount,
    replacement_cut_cost before after B b0 b1⟩

/-- Component-level degree propagates to the occupied nonterminal piece before
the complete actual partition refinement is applied. -/
theorem actual_component_partition_split (t u : Tree)
    (before after : List (List Nat)) (B S : List Nat) (v : Vertex)
    (mt mu : Vertex → Prop) (hnt : (leaves t).Nodup)
    (h : agreement t u (before ++ B :: after) = true)
    (hmt : AvoidsPartition t (before ++ B :: after) mt)
    (hmu : AvoidsPartition u (before ++ B :: after) mu)
    (hsub : ∀ x, x ∈ B → x ∈ S)
    (hv : v ∈ minimalVertices B t) (hvnt : v ∉ terminals B t)
    (hdegree : actualDegree t S v = 2) :
    ∃ b0 b1 : List Nat, b0 ≠ [] ∧ b1 ≠ [] ∧ (b0 ++ b1).Perm B ∧
      agreement t u (before ++ b0 :: b1 :: after) = true ∧
      ¬ Occupied t (before ++ b0 :: b1 :: after) v ∧
      AvoidsPartition t (before ++ b0 :: b1 :: after) mt ∧
      AvoidsPartition u (before ++ b0 :: b1 :: after) mu ∧
      (before ++ b0 :: b1 :: after).length = (before ++ B :: after).length + 1 ∧
      (before ++ b0 :: b1 :: after).length - 1 =
        ((before ++ B :: after).length - 1) + 1 :=
  actual_partition_split t u before after B v mt mu hnt h hmt hmu
    (actualDegree_propagation B S t v hsub hv hvnt hdegree)

end DegreeTwo
