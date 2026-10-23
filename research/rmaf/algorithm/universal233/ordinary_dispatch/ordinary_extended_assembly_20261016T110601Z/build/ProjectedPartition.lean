import EdgeSides
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem clip_cons_nonempty (X B : List Nat) (F : List (List Nat))
    (hn : B.filter (X.contains ·)≠[]) :
    clip X (B::F)=B.filter (X.contains ·)::clip X F := by
  have he : (B.filter (X.contains ·)).isEmpty=false := by
    cases h : (B.filter (X.contains ·)).isEmpty with
    | false => rfl
    | true => exact False.elim (hn (List.isEmpty_iff.1 h))
  simp only [clip,List.filterMap_cons,clipBlock,he,Bool.false_eq_true,ite_false]

theorem partition_attach_marker (X K : List Nat) (F : List (List Nat)) (y : Nat)
    (hp : partitionCheck X (K::F)=true) (hn : y∉X) :
    partitionCheck (y::X) ((K++[y])::F)=true := by
  have ny : y∉(K::F).flatten := fun h =>
    hn (Universal233.SourceCoverage.partitionCheck_subset X (K::F) hp h)
  have count : ∀x,((K++[y])::F).flatten.count x=(K::F).flatten.count x+[y].count x := by
    intro x
    simp only [List.flatten_cons,List.count_append]
    omega
  apply BinaryExchange.partition_intro
  · intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · intro h
      have : [y]=[] := (List.append_eq_nil_iff.1 h).2
      contradiction
    · exact checked_nonempty X (K::F) hp B (List.mem_cons_of_mem K hB)
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [count,List.count_eq_zero.2 ny]
      simp
    · rw [count,checked_count X (K::F) hp hx]
      have he : y≠x := by intro he;subst x;exact hn hx
      simp [he]
  · intro x hx
    simp only [List.flatten_cons,List.mem_append,List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact List.mem_cons_of_mem y (checked_label X (K::F) hp (by simp) hx)
    · simp
    · exact List.mem_cons_of_mem y (Universal233.SourceCoverage.partitionCheck_subset X (K::F) hp
        (List.mem_append_right K hx))

theorem original_crossing_topology (T S : Tree) (X Y B : List Nat) (y m : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (subT : B⊆leaves T) (subS : B⊆leaves S)
    (neX : B.filter (X.contains ·)≠[]) (neY : B.filter (Y.contains ·)≠[])
    (hy : y∈Y) (freshT : m∉leaves T) (freshS : m∉leaves S)
    (ha : restrictionAgrees T S B=true) :
    restrictionAgrees T S (B.filter (X.contains ·)++[y])=true := by
  obtain ⟨zT,zS,hzT,hzS,hi⟩ := original_crossing_projection T S X Y B y m ndT ndS
    hpT hpS edgeT edgeS subT subS neX neY hy freshT freshS ha
  have hb := relabel_iso (swap y m) hi
  rw [relabel_twice _ (swap_involution y m),relabel_twice _ (swap_involution y m)] at hb
  simpa only [restrictionAgrees,hzT,hzS] using (sameShape_correct zT zS).2 hb
end OrdinaryCommonSplit
