import DisjointQuery
namespace OrdinaryDispatch.DisjointParents
open RMAF RestrictionBridge ForestState OutputState Universal233 Universal233.CherryBranching Universal233.BothBad

/-- A specific covered source child suffices; no whole-family cover is assumed. -/
theorem member_complete (actual : Ordinary) (T S : Tree) (k : Nat) (cs : List Child)
 (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) (c : Child) (hc : c∈cs)
 (part : partitionCheck (leaves S) c.partition=true)
 (emb : pairwiseEmbeddings S c.partition=true)
 (paid : c.paid+1=c.partition.length)
 (mat : c.sourceForest=OutputState.sourceForest S c.partition)
 (ih : ∀r,remaining k c=some r → ForestMinCompletion.LocalOrdinaryIH r actual)
 (F : OrdinaryDispatch.Forest) (hf : feasible T S c F) (budget : F.length-1≤k) :
 ∃G,runChildren actual T S k cs=some G ∧ G.length≤F.length := by
 obtain ⟨r,hr,hwithin⟩ := (remaining_correct k part emb paid).1 ⟨F,hf,budget⟩
 have ex := forest_child_exact_at T S c r actual (ih r hr) nt ns same part emb mat
 obtain ⟨G,hG⟩ := ex.1.2 hwithin
 have hs := ex.2 G hG
 have accept : ordinaryAccepted T S k G=true := by
  have hrefLen := refined_length part emb hs.1.1.1 hs.1.1.2
  have rem : c.paid≤k ∧ r=k-c.paid := by
   unfold remaining at hr
   split at hr
   · exact ⟨by assumption,Option.some.inj hr.symm⟩
   · contradiction
  simp only [ordinaryAccepted,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨hs.1.1.1,by omega⟩
 have mem : G∈childAnswers actual T k cs := List.mem_filterMap.2 ⟨c,hc,by simp [childCall,hr,hG]⟩
 obtain ⟨H,hH⟩ := best_exists List.length (ordinaryAccepted T S k) _ G mem accept
 have min := (best_spec List.length (ordinaryAccepted T S k) _ H hH).2.2 G mem accept
 exact ⟨H,hH,Nat.le_trans min (hs.1.2 F hf)⟩

theorem run_sound (actual : Ordinary) (T S : Tree) (a b q : Nat) (F : OrdinaryDispatch.Forest)
 (h : run actual T S a b q=some F) : agreement T S F=true ∧ F.length-1≤q := by
 rcases choose_origin _ _ F h with h|h
 · exact runChildren_sound actual T S q _ F h
 · exact query_sound actual T S _ F q h

/-- The ordinary cherry source cover is consumed with exactly two unit calls
and the literal parent query. Only that actual query remains a named premise. -/
theorem run_complete_from_parent (actual : Ordinary) (T S : Tree) (a b q : Nat)
 {p : RMAF.Vertex} (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) (ch : CoreGraph.CherryAt T p a b)
 (ih : ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual)
 (parent : ∀F,agreement T S F=true → Refines F (pendantPartition S a b) → F.length-1≤q →
  ∃G,(query actual T S (pendantPartition S a b) q).answer=some G ∧ G.length≤F.length)
 (F : OrdinaryDispatch.Forest) (hf : agreement T S F=true) (budget : F.length-1≤q) :
 ∃G,run actual T S a b q=some G ∧ G.length≤F.length := by
 obtain ⟨c,hc,hfeas⟩ := ordinary_branches_cover ns hf ch
 have cases : c=singletonChild S a ∨ c=singletonChild S b ∨ c=pendantChild S a b := by
  simpa [branches] using hc
 rcases cases with ha|hb|hp
 · subst c
   obtain ⟨part,emb,paid,mat⟩ := three_children_literal nt ns same ch _ hc
   obtain ⟨H,hH,hmin⟩ := member_complete actual T S q [singletonChild S a,singletonChild S b]
    nt ns same _ (by simp) part emb paid mat
    (fun r hr=>ih r (remaining_decreases (Nat.le_refl 1 : 1≤(singletonChild S a).paid) hr)) F hfeas budget
   obtain ⟨G,hG,hGH⟩ := choose_left_min _ _ H hH
   exact ⟨G,hG,Nat.le_trans hGH hmin⟩
 · subst c
   obtain ⟨part,emb,paid,mat⟩ := three_children_literal nt ns same ch _ hc
   obtain ⟨H,hH,hmin⟩ := member_complete actual T S q [singletonChild S a,singletonChild S b]
    nt ns same _ (by simp) part emb paid mat
    (fun r hr=>ih r (remaining_decreases (Nat.le_refl 1 : 1≤(singletonChild S b).paid) hr)) F hfeas budget
   obtain ⟨G,hG,hGH⟩ := choose_left_min _ _ H hH
   exact ⟨G,hG,Nat.le_trans hGH hmin⟩
 · subst c
   obtain ⟨H,hH,hmin⟩ := parent F hf hfeas.2 budget
   obtain ⟨G,hG,hGH⟩ := choose_right_min _ _ H hH
   exact ⟨G,hG,Nat.le_trans hGH hmin⟩
end OrdinaryDispatch.DisjointParents
