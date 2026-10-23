import MarkedProjection
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge Universal233.CoreGraph

theorem Port.restrict_selected_subtree (c : Port) (u v : Tree) (L : List Nat)
    (nd : (leaves (c.plug u)).Nodup) (sub : L⊆leaves u) (hv : restrict L u=some v) :
    restrict L (c.plug u)=some v := by
  have sep := (List.nodup_append.1 ((c.leaves_perm u).nodup_iff.1 nd)).2.2
  have hc : (c.clip L).labels=[] := by
    rw [Port.clip_labels]
    apply List.filter_eq_nil_iff.2
    intro x hx
    have hn : x∉L := fun hm => sep x hx x (sub hm) rfl
    simp [hn]
  have he : c.clip L=.hole := (c.clip L).empty_labels hc
  simpa only [he,Port.plug] using c.restrict_plug u v L hv

theorem nonempty_restriction_topology (T S : Tree) (K L : List Nat) (x : Nat)
    (ne : L≠[]) (sub : L⊆leaves T) (h : restrictionAgrees T S (L++[x])=true) :
    restrictionAgrees T S L=true := by
  obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil L ne
  exact BinaryExchange.restrictionAgrees_sub T S _ L h
    (by intro z hz;exact List.mem_append_left _ hz) ⟨y,hy,sub hy⟩

theorem original_glue_descendant_Y (T S uT uS : Tree) (pT pS : RMAF.Vertex)
    (X Y K L : List Nat) (y : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : subtree T pT=some uT) (hpS : subtree S pS=some uS)
    (partT : partitionCheck (leaves T) [X,Y]=true) (partS : partitionCheck (leaves S) [X,Y]=true)
    (sideT : (leaves uT).Perm Y) (sideS : (leaves uS).Perm Y)
    (subK : K⊆X) (subL : L⊆Y) (neL : L≠[]) (hy : y∈Y)
    (hmark : restrictionAgrees T S (K++[y])=true) (htopo : restrictionAgrees T S L=true) :
    restrictionAgrees T S (K++L)=true := by
  obtain ⟨l,hl⟩ := List.exists_mem_of_ne_nil L neL
  have subLT : L⊆leaves uT := fun _ hx => sideT.mem_iff.2 (subL hx)
  have subLS : L⊆leaves uS := fun _ hx => sideS.mem_iff.2 (subL hx)
  obtain ⟨vT,hvT⟩ := restriction_exists uT L ⟨l,subLT hl,hl⟩
  obtain ⟨vS,hvS⟩ := restriction_exists uS L ⟨l,subLS hl,hl⟩
  obtain ⟨c,hc⟩ := original_port T uT pT hpT
  obtain ⟨d,hd⟩ := original_port S uS pS hpS
  have rt : restrict L T=some vT := by rw [hc];exact c.restrict_selected_subtree uT vT L (hc ▸ ndT) subLT hvT
  have rs : restrict L S=some vS := by rw [hd];exact d.restrict_selected_subtree uS vS L (hd ▸ ndS) subLS hvS
  have hi : RootedIso vT vS := by
    apply (sameShape_correct _ _).1
    simpa only [restrictionAgrees,rt,rs] using htopo
  exact original_cut_topology_glue T S uT uS vT vS pT pS K L y ndT ndS hpT hpS
    (by intro z hz hzK;exact split_disjoint _ X Y partT z (subK hzK) (sideT.mem_iff.1 hz))
    (by intro z hz hzK;exact split_disjoint _ X Y partS z (subK hzK) (sideS.mem_iff.1 hz))
    subLT subLS (sideT.mem_iff.2 hy) (sideS.mem_iff.2 hy) hvT hvS hi hmark

theorem original_glue_mixed (T S uY uX : Tree) (pT pS : RMAF.Vertex)
    (X Y K L : List Nat) (x y : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (hpT : subtree T pT=some uY) (hpS : subtree S pS=some uX)
    (partT : partitionCheck (leaves T) [X,Y]=true) (partS : partitionCheck (leaves S) [X,Y]=true)
    (sideT : (leaves uY).Perm Y) (sideS : (leaves uX).Perm X)
    (subK : K⊆X) (subL : L⊆Y) (neK : K≠[]) (neL : L≠[]) (hx : x∈X) (hy : y∈Y)
    (hmarkX : restrictionAgrees T S (K++[y])=true)
    (hmarkY : restrictionAgrees T S (L++[x])=true) : restrictionAgrees T S (K++L)=true := by
  obtain ⟨c,hc⟩ := original_port T uY pT hpT
  obtain ⟨d,hd⟩ := original_port S uX pS hpS
  have partS' : partitionCheck (leaves S) [Y,X]=true :=
    BinaryExchange.partition_perm _ _ _ (List.Perm.swap X Y []).symm partS
  have ctxT := c.labels_of_cut uY X Y (hc ▸ ndT) (hc ▸ partT) sideT
  have ctxS := d.labels_of_cut uX Y X (hd ▸ ndS) (hd ▸ partS') sideS
  have sk : K⊆leaves uX := fun _ hk => sideS.mem_iff.2 (subK hk)
  have sl : L⊆leaves uY := fun _ hl => sideT.mem_iff.2 (subL hl)
  obtain ⟨k,hk⟩ := List.exists_mem_of_ne_nil K neK
  obtain ⟨l,hl⟩ := List.exists_mem_of_ne_nil L neL
  obtain ⟨vX,hvX⟩ := restriction_exists uX K ⟨k,sk hk,hk⟩
  obtain ⟨vY,hvY⟩ := restriction_exists uY L ⟨l,sl hl,hl⟩
  have hh := mixed_port_topology_glue c d uY uX vY vX K L x y
    (hc ▸ ndT) (hd ▸ ndS) sk sl
    (by intro z hz hzK;exact split_disjoint _ X Y partT z (subK hzK) (sideT.mem_iff.1 hz))
    (by intro z hz hzL;exact split_disjoint _ X Y partS z (sideS.mem_iff.1 hz) (subL hzL))
    ((ctxT x).2 hx) (sideS.mem_iff.2 hx) ((ctxS y).2 hy) (sideT.mem_iff.2 hy) hvX hvY
    (by simpa only [←hc,←hd] using hmarkX) (by simpa only [←hc,←hd] using hmarkY)
  simpa only [←hc,←hd] using hh

/-- Full original common-cut topology gluing. All four original cut
orientations and arbitrary representative positions are covered. -/
theorem original_union_glue (T S : Tree) (X Y K L : List Nat) (x y : Nat)
    (ndT : (leaves T).Nodup) (ndS : (leaves S).Nodup)
    (partT : partitionCheck (leaves T) [X,Y]=true) (partS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (subK : K⊆X) (subL : L⊆Y) (neK : K≠[]) (neL : L≠[]) (hx : x∈X) (hy : y∈Y)
    (hmarkX : restrictionAgrees T S (K++[y])=true)
    (hmarkY : restrictionAgrees T S (L++[x])=true) : restrictionAgrees T S (K++L)=true := by
  obtain ⟨pT,uT,_,hpT,sideT⟩ := edgeT
  obtain ⟨pS,uS,_,hpS,sideS⟩ := edgeS
  rcases sideT with ty | tx <;> rcases sideS with sy | sx
  · have lsub : L⊆leaves T := fun _ hz => (split_labels _ X Y partT _).2 (Or.inr (subL hz))
    have ltop := nonempty_restriction_topology T S K L x neL lsub hmarkY
    exact original_glue_descendant_Y T S uT uS pT pS X Y K L y ndT ndS hpT hpS partT partS
      ty sy subK subL neL hy hmarkX ltop
  · exact original_glue_mixed T S uT uS pT pS X Y K L x y ndT ndS hpT hpS partT partS
      ty sx subK subL neK neL hx hy hmarkX hmarkY
  · apply Universal233.PairAssembly.restriction_agrees_swap S T
    exact original_glue_mixed S T uS uT pS pT X Y K L x y ndS ndT hpS hpT partS partT
      sy tx subK subL neK neL hx hy
      (Universal233.PairAssembly.restriction_agrees_swap T S _ hmarkX)
      (Universal233.PairAssembly.restriction_agrees_swap T S _ hmarkY)
  · have ksub : K⊆leaves T := fun _ hz => (split_labels _ X Y partT _).2 (Or.inl (subK hz))
    have ktop := nonempty_restriction_topology T S L K y neK ksub hmarkX
    have partT' : partitionCheck (leaves T) [Y,X]=true :=
      BinaryExchange.partition_perm _ _ _ (List.Perm.swap X Y []).symm partT
    have partS' : partitionCheck (leaves S) [Y,X]=true :=
      BinaryExchange.partition_perm _ _ _ (List.Perm.swap X Y []).symm partS
    have hh := original_glue_descendant_Y T S uT uS pT pS Y X L K x ndT ndS hpT hpS partT' partS'
      tx sx subL subK neK hx hmarkY ktop
    have rT := Universal233.DepthOne.restrict_members T (L++K) (K++L)
      (by intro z;simp only [List.mem_append];exact or_comm)
    have rS := Universal233.DepthOne.restrict_members S (L++K) (K++L)
      (by intro z;simp only [List.mem_append];exact or_comm)
    simpa only [restrictionAgrees,rT,rS] using hh
end OrdinaryCommonSplit
