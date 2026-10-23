import BuildSetup
namespace OrdinaryCommonSplit.Source
open RMAF Universal233 CoreGraph RestrictionBridge Caller

theorem buildSetup_complete (T S u : Tree) (X Y : List Nat) (p q : RMAF.Vertex)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (nonroot : p≠[]) (source : subtree S p=some u) (labels : (leaves u).Perm X)
    (boundary : incident T X=[q]) : ∃d,buildSetup T S X Y p=some d := by
  let x := X.headD 0
  let y := Y.headD 0
  let L := leaves T++leaves S
  let rho := labelMax L+1
  let gamma := labelMax L+2
  have hx : x∈X := headD_mem X (checked_nonempty _ _ hpT X (by simp))
  have hy : y∈Y := headD_mem Y (checked_nonempty _ _ hpT Y (by simp))
  have nx := checked_block_nodup _ _ hpT X (by simp)
  have ny := checked_block_nodup _ _ hpT Y (by simp)
  have sXT : X⊆leaves T := fun _ h => (split_labels _ X Y hpT _).2 (Or.inl h)
  have sXS : X⊆leaves S := fun _ h => (split_labels _ X Y hpS _).2 (Or.inl h)
  have sYT : Y⊆leaves T := fun _ h => (split_labels _ X Y hpT _).2 (Or.inr h)
  have sYS : Y⊆leaves S := fun _ h => (split_labels _ X Y hpS _).2 (Or.inr h)
  have ynot : y∉X := by intro h;exact split_disjoint _ X Y hpT y h hy
  have xnot : x∉Y := split_disjoint _ X Y hpT x hx
  have frT : rho∉leaves T := fun h=>fresh_not_mem L 1 (by decide) (List.mem_append_left _ h)
  have frS : rho∉leaves S := fun h=>fresh_not_mem L 1 (by decide) (List.mem_append_right _ h)
  have fgT : gamma∉leaves T := fun h=>fresh_not_mem L 2 (by decide) (List.mem_append_left _ h)
  have fgS : gamma∉leaves S := fun h=>fresh_not_mem L 2 (by decide) (List.mem_append_right _ h)
  obtain ⟨tx,htx⟩ := restriction_exists T X ⟨x,sXT hx,hx⟩
  obtain ⟨sx,hsx⟩ := restriction_exists S X ⟨x,sXS hx,hx⟩
  obtain ⟨ty,hty⟩ := restriction_exists T Y ⟨y,sYT hy,hy⟩
  obtain ⟨sy,hsy⟩ := restriction_exists S Y ⟨y,sYS hy,hy⟩
  obtain ⟨mxT,hMXT,_,_⟩ := marked_labels T X y rho nt nx (sYT hy) ynot sXT frT
  obtain ⟨mxS,hMXS,_,_⟩ := marked_labels S X y rho ns nx (sYS hy) ynot sXS frS
  obtain ⟨myT,hMYT,_,_⟩ := marked_labels T Y x gamma nt ny (sXT hx) xnot sYT fgT
  obtain ⟨myS,hMYS,_,_⟩ := marked_labels S Y x gamma ns ny (sXS hx) xnot sYS fgS
  simp only [buildSetup,dite_eq_left nt,dite_eq_left ns,dite_eq_left hpT,dite_eq_left hpS,dite_eq_left nonroot]
  split
  · rename_i absent
    simp [source] at absent
  · rename_i v hv
    have eq : v=u := Option.some.inj (hv.symm.trans source)
    subst v
    simp only [dite_eq_left labels]
    split
    · rename_i r hr
      have eq : r=q := by simpa [boundary] using hr.symm
      subst r
      split
      · exact ⟨_,rfl⟩
      · rename_i impossible
        exact False.elim (impossible tx sx ty sy mxT mxS myT myS htx hsx hty hsy hMXT hMXS hMYT hMYS)
    · rename_i hbad
      simp [boundary] at hbad
end OrdinaryCommonSplit.Source
