import PretestConsumer
namespace Universal233.BinaryCheap
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

def TwoBad (S T : Tree) (o : Output) : Prop :=
  ∃ K L, K ∈ o.partition ∧ L ∈ o.partition ∧ K ≠ L ∧
    restrictionAgrees S T K = false ∧ restrictionAgrees S T L = false ∧ Disj T K L

def OppositeSafe (S T : Tree) (A B C : List Nat) (a o : Output) : Prop :=
  RefinesBlocks o.partition [A,B,C] ∧
  KeptParent.Keeps A o ∧ KeptParent.Keeps C o ∧
  (∃ K, K ∈ o.partition ∧ SameMembers K A ∧
    restrict K S = restrict A S ∧ restrict K T = restrict A T ∧
    KeptParent.OriginalLocalOneCut S T K a) ∧
  (∀ L, L ∈ o.partition → Sub L B → Disj T L A ∧ Disj T L C) ∧ Disj T A C

/-- Complete scoped A-cheap consumer of the actual selected edge and q3 probe.
The original hypotheses are printed; every graph/cost field below is derived.
The final query/reconstruction and the global recurrence are later consumers. -/
theorem selected_cheap_continuation (S T : Tree) (A B C : List Nat)
    (e : RMAF.Vertex × RMAF.Vertex)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves S ↔ x ∈ leaves T)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hsource : pairwiseEmbeddings S [A,B,C] = true)
    (hbadA : restrictionAgrees S T A = false) (hbadB : restrictionAgrees S T B = false)
    (hgoodC : restrictionAgrees S T C = true)
    (hchoose : PairGeometry.choose T A B = some (.edge e))
    (hac : Disj T A C) (hbc : Disj T B C)
    (haccept : fourAccepted S (cheapColor A B (PairGeometry.descendants T e.2)) = true) :
    ∃ u o, treeAt T e.2 = some u ∧
      sideOutputs S B A (PairGeometry.descendants T e.2) 3 = [o] ∧
      o.sourceCuts.length = 3 ∧ o.partition.length = 4 ∧
      partitionCheck (leaves S) o.partition = true ∧ pairwiseEmbeddings S o.partition = true ∧
      pairwiseEmbeddings T o.partition = true ∧
      (∀ K, K ∈ o.partition → ∃ L, L ∈ classes A B C (leaves u) ∧ SameMembers K L) ∧
      (∀ L, L ∈ classes A B C (leaves u) → ∃ K, K ∈ o.partition ∧ SameMembers K L) ∧
      (∃ K, K ∈ o.partition ∧ SameMembers K C ∧ restrictionAgrees S T K = true) ∧
      (∀ q, 3 ≤ q → sideOutputs S B A (PairGeometry.descendants T e.2) q = [o]) ∧
      (restrictionAgrees S T (ay A (leaves u)) = true →
       restrictionAgrees S T (an A (leaves u)) = true →
       ∃ s t p, restrict A S = some s ∧ restrict A T = some t ∧
         DepthOne.pretest01 t s = .found (some p) ∧
         KeptParent.OriginalLocalOneCut S T A ⟨DepthOne.forest s (some p),[p]⟩ ∧
         (∀ H, agreement t s H = true → 1 ≤ H.length-1) ∧
         (∀ q z, z ∈ sideOutputs S A B (PairGeometry.descendants T e.2) q →
           OppositeSafe S T A B C ⟨DepthOne.forest s (some p),[p]⟩ z)) ∧
      (¬(restrictionAgrees S T (ay A (leaves u)) = true ∧
         restrictionAgrees S T (an A (leaves u)) = true) → TwoBad S T o) := by
  obtain ⟨u,o,hu,hout,hcost,hlen,hpart,hsrc,htgt,hforward,hback,hall⟩ :=
    selected_accepted_partition S T A B C e hs ht same hp hchoose hac hbc haccept
  obtain ⟨v,hv,hay,han,hby,hbn,cay,can,cby,cbn,hsepA,hsepB⟩ := edge_facts T A B e hchoose
  have he : v = u := Option.some.inj (hv.symm.trans hu)
  subst v
  obtain ⟨KC,hKC,hKCC⟩ := hback C (by simp [classes])
  have hKCgood : restrictionAgrees S T KC = true :=
    (KeptParent.restriction_agrees_same_members S T KC C hKCC).trans hgoodC
  refine ⟨u,o,hu,hout,hcost,hlen,hpart,hsrc,htgt,hforward,hback,⟨KC,hKC,hKCC,hKCgood⟩,hall,?_,?_⟩
  · intro hgy hgn
    obtain ⟨s,t,p,hrs,hrt,hfound,hcert,hmin⟩ := cheap_good_sectors_pretest S T A B C (leaves u) o
      hs ht same hp hbadA hay han hsrc hback hsepA hgy hgn
    refine ⟨s,t,p,hrs,hrt,hfound,hcert,hmin,?_⟩
    intro q z hz
    have heq := side_outputs_descendant S T u A B e.2 ht hu q
    rw [heq] at hz
    obtain ⟨hab,hacLabels,hbcLabels⟩ := Assembly.parent_partition_disjoint S A B C hp
    exact ⟨Assembly.tagged_output_refines_parents S A B C (fun _ => 0) (sideColor (leaves u))
      (fun _ => 0) q z hz hp hab hacLabels hbcLabels,
      every_opposite_output S T A B C (leaves u) hp hsource cby cbn hac hbc _ hcert q z hz⟩
  · intro hn
    have hb : restrictionAgrees S T (ay A (leaves u)) = false ∨
        restrictionAgrees S T (an A (leaves u)) = false := by
      cases hy : restrictionAgrees S T (ay A (leaves u)) <;>
        cases hn' : restrictionAgrees S T (an A (leaves u)) <;> simp_all
    exact cheap_two_bad S T A B C (leaves u) o hp hbadB hay han hb cay can hback
end Universal233.BinaryCheap
