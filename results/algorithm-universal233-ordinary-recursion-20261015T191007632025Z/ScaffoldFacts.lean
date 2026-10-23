import OrdinaryScaffold
namespace OrdinaryScaffold
open RMAF RestrictionBridge ForestState Universal233 Universal233.CherryBranching OrdinaryDispatch

theorem ordinary_state_proper {T S : Tree} (hp : DepthOne.proper T S=true) :
 ForestState.proper (some T) [S]=true := by
 obtain ⟨nt,ns,perm⟩ := (DepthOne.proper_iff T S).1 hp
 simp only [ForestState.proper,labels,Bool.and_eq_true,decide_eq_true_eq,List.map_cons,List.map_nil]
 refine ⟨decide_eq_true nt,partition_by_counts _ _ nt ?_ ?_⟩
 · intro B hB
   have eq : B=leaves S := by simpa using hB
   simpa [eq] using leaves_nonempty S
 · intro x
   simpa using (perm.count_eq x).symm

theorem select_none_candidates_nil {T S : Tree} (h : select T S=none) : candidates T S=[] := by
 unfold select at h
 cases h0 : (candidates T S).find? (fun c=>c.originalCuts.isEmpty) with
 | some c => simp [h0] at h
 | none =>
  cases h1 : (candidates T S).find? (fun c=>c.originalCuts.length==1) with
  | some c => simp [h0,h1] at h
  | none =>
   cases h3 : (candidates T S).find? (fun c=>decide (3≤c.originalCuts.length)) with
   | some c => simp [h0,h1,h3] at h
   | none =>
    have hh : (candidates T S).head?=none := by
     cases hc : (candidates T S).head? <;> simp_all
    exact List.head?_eq_none_iff.1 hh

theorem select_none_leaf {T S : Tree} (h : select T S=none) : ∃a,T=.leaf a := by
 rcases Rule5Classification.tree_leaf_or_cherry T with leaf | ⟨p,a,b,ch⟩
 · exact leaf
 · have hm : (⟨p,a,b,cuts S a b⟩ : Candidate)∈candidates T S :=
    List.mem_map.2 ⟨(p,a,b),cherries_complete T p a b ch,rfl⟩
   rw [select_none_candidates_nil h] at hm
   contradiction

theorem leaf_not_rejected (a : Nat) {S : Tree} (hp : DepthOne.proper (.leaf a) S=true) :
 DepthOne.pretest01 (.leaf a) S≠.rejected := by
 have perm := ((DepthOne.proper_iff (.leaf a) S).1 hp).2.2
 have es : leaves S=[a] := List.perm_singleton.1 perm.symm
 have se : S=.leaf a := tree_of_singleton_leaves S a es
 subst S
 have af : agreement (.leaf a) (.leaf a) [[a]]=true := by
  simp [agreement,leaves,partitionCheck,restrictionAgrees,restrict,sameShape,pairwiseEmbeddings]
 intro rejected
 have no := DepthOne.rejected_lower_bound (.leaf a) (.leaf a) rejected [[a]] af
 simp at no

theorem select_after_rejection {T S : Tree} (hp : DepthOne.proper T S=true)
 (rej : DepthOne.pretest01 T S=.rejected) : ∃s,select T S=some s := by
 cases hs : select T S with
 | some s => exact ⟨s,rfl⟩
 | none =>
  obtain ⟨a,rfl⟩ := select_none_leaf hs
  exact False.elim (leaf_not_rejected a hp rej)

theorem query_sound {T S : Tree} {q : Nat} {answer : Option CommonForest}
 (h : QueryExact T S q answer) {G : CommonForest} (hg : answer=some G) :
 agreement T S G=true ∧ G.length-1≤q ∧ ∀F,agreement T S F=true →G.length≤F.length := by
 simpa only [hg,QueryExact] using h

theorem query_complete {T S : Tree} {q : Nat} {answer : Option CommonForest}
 (h : QueryExact T S q answer) (F : CommonForest) (ha : agreement T S F=true)
 (cost : F.length-1≤q) : ∃G,answer=some G := by
 cases answer with
 | none => have impossible := h F ha; omega
 | some G => exact ⟨G,rfl⟩

theorem query_of_checked_complete {T S : Tree} {q : Nat} (answer : Option CommonForest)
 (sound : ∀G,answer=some G →agreement T S G=true ∧ G.length-1≤q)
 (complete : ∀F,agreement T S F=true →F.length-1≤q →∃G,answer=some G ∧ G.length≤F.length) :
 QueryExact T S q answer := by
 cases answer with
 | none =>
  intro F ha
  by_cases budget : F.length-1≤q
  · obtain ⟨G,hG,_⟩ := complete F ha budget
    contradiction
  · omega
 | some G =>
  have hs := sound G rfl
  refine ⟨hs.1,hs.2,?_⟩
  intro F ha
  by_cases budget : F.length-1≤q
  · obtain ⟨H,hH,least⟩ := complete F ha budget
    have eq : G=H := Option.some.inj hH
    simpa [eq] using least
  · omega

theorem found_query_exact (T S : Tree) (q : Nat) (c : Option RMAF.Vertex)
 (hc : DepthOne.pretest01 T S=.found c) :
 QueryExact T S q (if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none) := by
 have hs := DepthOne.found_globally_minimum T S c hc
 by_cases cost : DepthOne.cutCost c≤q
 · simp only [cost,if_pos,QueryExact]
   refine ⟨hs.1,by omega,?_⟩
   intro F hF
   have least := hs.2.2 F hF
   have positive := List.length_pos_iff.2 (DepthOne.agreement_nonempty T S F hF)
   omega
 · simp only [cost,if_neg,QueryExact]
   intro F hF
   have least := hs.2.2 F hF
   omega
end OrdinaryScaffold
