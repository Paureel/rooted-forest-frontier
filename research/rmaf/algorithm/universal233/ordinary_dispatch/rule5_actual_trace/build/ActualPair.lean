import TwoGroupComplete
import GroupPriority
namespace OrdinaryDispatch.GoodPairDP
open RMAF ForestState ForestGroups RestrictionBridge Universal233 VertexGeometry

theorem local_source_good (T S u s : Tree) (P : Forest) (U K : List Nat)
 (hs : (leaves S).Nodup) (hP : partitionCheck (leaves S) P=true)
 (hK : K∈P) (ru : restrict U T=some u) (rs : restrict K S=some s)
 (sub : K⊆U) (good : restrictionAgrees T S K=true) :
 targetAgrees (some u) s (leaves s)=true := by
 have ls := component_labels S s K P rs hs hP hK
 have inU : leaves s⊆U := fun x hx=>sub (ls.mem_iff.1 hx)
 have rt : restrict (leaves s) u=restrict K T :=
  (restrict_inside T u U (leaves s) ru inU).trans
   (KeptParent.restrict_same_members (leaves s) K (fun _=>ls.mem_iff) T)
 have self : restrict (leaves s) s=some s := restrict_of_contains s _
  (fun _ hx=>List.contains_iff_mem.2 hx)
 simpa only [targetAgrees,restrictionAgrees,rt,self,rs] using good

/-- All geometry and positivity come from the literal original three parents;
no all-good or positive-minimum field is assumed for the constructed AB job. -/
theorem actual_good_pair (T S : Tree) (A B C : List Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (hac : BinaryExchange.Disj T A C) (hbc : BinaryExchange.Disj T B C)
 (ga : restrictionAgrees T S A=true) (gb : restrictionAgrees T S B=true)
 (over : ∃v,v∈minimalVertices A T ∧ v∈minimalVertices B T) :
 let ss := OutputState.sourceForest S [A,B,C]
 AllGoodDP.allGood (localTarget (some T) (A++B)) (owned ss (A++B))=true ∧
 ∀F,agrees (localTarget (some T) (A++B)) (owned ss (A++B)) F=true →
  0<additionalCost (owned ss (A++B)) F := by
 have ref : SourceCoverage.RefinesBlocks [A,B,C] [A,B,C] :=
  fun K hk=>⟨K,hk,List.Subset.refl _⟩
 obtain ⟨proper,hq,own,cross⟩ := GroupedFullQuery.abc_geometry T S [A,B,C] A B C hs ht same hp hp ref hac hbc
 obtain ⟨a,ra,la⟩ := OutputState.checked_restrictions S [A,B,C] hs hp A (by simp)
 obtain ⟨b,rb,lb⟩ := OutputState.checked_restrictions S [A,B,C] hs hp B (by simp)
 obtain ⟨c,rc,lc⟩ := OutputState.checked_restrictions S [A,B,C] hs hp C (by simp)
 have mat : OutputState.sourceForest S [A,B,C]=[a,b,c] := by simp [OutputState.sourceForest,ra,rb,rc]
 have inA : leaves a⊆A := fun _ hx=>la.mem_iff.1 hx
 have inB : leaves b⊆B := fun _ hx=>lb.mem_iff.1 hx
 have inC : leaves c⊆C := fun _ hx=>lc.mem_iff.1 hx
 have AB : A++B≠C := by
  have nd := checked_family_nodup _ _ hq
  simpa using (List.nodup_cons.1 nd).1
 have ownAB : owned (OutputState.sourceForest S [A,B,C]) (A++B)=[a,b] := by
  rw [mat]
  change owned ([a,b]++[c]) (A++B)=[a,b]
  rw [owned_append,owned_within [a,b] (A++B) (by
   intro s h;rcases List.mem_cons.1 h with rfl|h
   · exact fun x hx=>List.mem_append_left B (inA hx)
   · have eq : s=b := by simpa using h
     subst s
     exact fun x hx=>List.mem_append_right A (inB hx)),
   owned_outside _ _ hq (A++B) C (by simp) (by simp) AB [c] (by simpa using inC)]
  simp
 have localProper := local_proper _ _ _ proper hq own (A++B) (by simp)
 obtain ⟨t,u,eq,ru,localEq,lu⟩ := group_target _ _ _ proper hq (A++B) (by simp)
 have et : t=T := Option.some.inj eq.symm
 subst t
 have goodA := local_source_good T S u a [A,B,C] (A++B) A hs hp (by simp) ru ra
  (fun _ hx=>List.mem_append_left B hx) ga
 have goodB := local_source_good T S u b [A,B,C] (A++B) B hs hp (by simp) ru rb
  (fun _ hx=>List.mem_append_right A hx) gb
 refine ⟨?_,?_⟩
 · simp only [AllGoodDP.allGood,Bool.and_eq_true]
   exact ⟨localProper,by simpa [ownAB,localEq] using And.intro goodA goodB⟩
 · intro F hf
   by_cases pos : 0<additionalCost (owned (OutputState.sourceForest S [A,B,C]) (A++B)) F
   · exact pos
   have zero : additionalCost (owned (OutputState.sourceForest S [A,B,C]) (A++B)) F=0 := by omega
   obtain ⟨G,mem,_,valid,cost⟩ := ForestPretest01.universal_coverage _ _ F hf (by omega)
   have eg : G=ForestPretest01.unchanged (owned (OutputState.sourceForest S [A,B,C]) (A++B)) :=
    ForestPretest01.candidate_zero _ G mem (by omega)
   rw [eg] at valid
   have localE := (agrees_parts _ _ _ valid).2.2.2.1
   have eu : pairwiseEmbeddings u [leaves a,leaves b]=true := by
    simpa [ownAB,localEq,ForestPretest01.unchanged,targetEmbeddings] using localE
   have origE : pairwiseEmbeddings T [leaves a,leaves b]=true :=
    (pairwise_transport T u (A++B) [leaves a,leaves b] ru (by
     intro D hD
     rcases List.mem_cons.1 hD with rfl|hD
     · exact fun x hx=>List.mem_append_left B (inA hx)
     · have eq : D=leaves b := by simpa using hD
       subst D
       exact fun x hx=>List.mem_append_right A (inB hx))).2 eu
   have perm : ForestPretest01.ForestPerm [leaves a,leaves b] [A,B] := .cons la (.cons lb .nil)
   have eab : pairwiseEmbeddings T [A,B]=true := by
    rw [←ForestPretest01.embeddings_perm T _ _ perm]
    exact origE
   have disj : disjointVertices (minimalVertices A T) (minimalVertices B T)=true := by
    simpa [pairwiseEmbeddings] using eab
   obtain ⟨v,va,vb⟩ := over
   exact False.elim ((clear_iff _ _).1 disj v va vb)
end OrdinaryDispatch.GoodPairDP
