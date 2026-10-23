import ThreeOutside
namespace OrdinaryCommonSplit.Source
open RMAF Universal233 CoreGraph RestrictionBridge Caller

/-- Nonrefusal follows from actual original source/target guards. In
particular outside minimum one is DERIVED, not an input or record field. -/
theorem actual_source_nonrefusal (T S u : Tree) (X Y C : List Nat) (p q r : RMAF.Vertex)
    (a b c budget : Nat) (cb : Tree→Tree→Nat→Option Forest)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (nonroot : p≠[]) (source : subtree S p=some u) (labels : (leaves u).Perm X)
    (boundary : incident T X=[q])
    (three : partitionCheck (leaves T) [X,C,[c]]=true)
    (eT : pairwiseEmbeddings T [X,C,[c]]=true) (eS : pairwiseEmbeddings S [X,C,[c]]=true)
    (goodC : restrictionAgrees T S C=true) (cherry : HardParent.HasCherry a b T)
    (aY : a∈Y) (bY : b∈Y) (cY : c∈Y)
    (rNonroot : r≠[]) (rParent : r.dropLast∈minimalVertices [a,b] S)
    (rOutside : r∉minimalVertices [a,b] S) (cBelow : c∈HardParent.subtreeLabels S r) :
    ∃answer,runSource T S X Y p budget cb=some answer := by
  obtain ⟨d,hd⟩ := buildSetup_complete T S u X Y p q nt ns hpT hpS nonroot source labels boundary
  obtain ⟨ht,hs,hX,hY⟩ := buildSetup_identity T S X Y p d hd
  have three' : partitionCheck (leaves d.T) [d.X,C,[c]]=true := by simpa only [ht,hX] using three
  have eT' : pairwiseEmbeddings d.T [d.X,C,[c]]=true := by simpa only [ht,hX] using eT
  have eS' : pairwiseEmbeddings d.S [d.X,C,[c]]=true := by simpa only [hs,hX] using eS
  have goodC' : restrictionAgrees d.T d.S C=true := by simpa only [ht,hs] using goodC
  have cherry' : HardParent.HasCherry a b d.T := by simpa only [ht] using cherry
  have aY' : a∈d.Y := by simpa only [hY] using aY
  have bY' : b∈d.Y := by simpa only [hY] using bY
  have cY' : c∈d.Y := by simpa only [hY] using cY
  have parent' : r.dropLast∈minimalVertices [a,b] d.S := by simpa only [hs] using rParent
  have outside' : r∉minimalVertices [a,b] d.S := by simpa only [hs] using rOutside
  have below' : c∈HardParent.subtreeLabels d.S r := by simpa only [hs] using cBelow
  obtain ⟨_,minimum,_⟩ := actual_outside_one_from_three d C a b c r three' eT' eS' goodC' cherry'
    aY' bY' cY' rNonroot parent' outside' below'
  obtain ⟨answer,hanswer⟩ := (runGuarded_nonrefusal_iff d budget cb).2 minimum
  exact ⟨answer,by simpa only [runSource,hd,Option.bind_some] using hanswer⟩

theorem actual_source_bounded_solver (T S u : Tree) (X Y C : List Nat) (p q r : RMAF.Vertex)
    (a b c budget : Nat) (cb : Tree→Tree→Nat→Option Forest)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (nonroot : p≠[]) (source : subtree S p=some u) (labels : (leaves u).Perm X)
    (boundary : incident T X=[q])
    (three : partitionCheck (leaves T) [X,C,[c]]=true)
    (eT : pairwiseEmbeddings T [X,C,[c]]=true) (eS : pairwiseEmbeddings S [X,C,[c]]=true)
    (goodC : restrictionAgrees T S C=true) (cherry : HardParent.HasCherry a b T)
    (aY : a∈Y) (bY : b∈Y) (cY : c∈Y)
    (rNonroot : r≠[]) (rParent : r.dropLast∈minimalVertices [a,b] S)
    (rOutside : r∉minimalVertices [a,b] S) (cBelow : c∈HardParent.subtreeLabels S r)
    (ih : SourceIH T S X Y p budget cb) :
    ∃answer,runSource T S X Y p budget cb=some answer ∧ BoundedExact T S budget answer := by
  obtain ⟨answer,run⟩ := actual_source_nonrefusal T S u X Y C p q r a b c budget cb nt ns
    hpT hpS nonroot source labels boundary three eT eS goodC cherry aY bY cY rNonroot rParent rOutside cBelow
  exact ⟨answer,run,source_answer_exact T S X Y p budget cb answer ih run⟩
end OrdinaryCommonSplit.Source
