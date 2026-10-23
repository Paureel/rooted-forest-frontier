import MarkerNormal
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge VertexGeometry

theorem actual_split_embeddings (T : Tree) (X Y : List Nat)
    (nd : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (edge : OriginalSplit T X Y) : pairwiseEmbeddings T [X,Y]=true := by
  obtain ⟨p,b,inside,hX,hY⟩ := original_split_side_guards T X Y nd hp edge
  have hc : Clear (minimalVertices X T) (minimalVertices Y T) := by
    intro v hv hw
    exact side_opposite (cut_side_hull p b inside _ hX v ((minimalVertices_correct X T v).1 hv))
      (cut_side_hull p b (!inside) _ hY v ((minimalVertices_correct Y T v).1 hw))
  simpa only [pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_true] using (clear_iff _ _).2 hc

theorem two_local_reconstruction (T S tx sx ty sy : Tree) (X Y : List Nat)
    (FX FY : List (List Nat))
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (et : pairwiseEmbeddings T [X,Y]=true) (es : pairwiseEmbeddings S [X,Y]=true)
    (htx : restrict X T=some tx) (hsx : restrict X S=some sx)
    (hty : restrict Y T=some ty) (hsy : restrict Y S=some sy)
    (hx : agreement tx sx FX=true) (hy : agreement ty sy FY=true) :
    agreement T S (FX++FY)=true := by
  let G : List Nat→List (List Nat) := fun U => if U=X then FX else FY
  let t : List Nat→Tree := fun U => if U=X then tx else ty
  let s : List Nat→Tree := fun U => if U=X then sx else sy
  have neq : Y≠X := Ne.symm (split_ne _ X Y hpT)
  have rt : ∀U∈[X,Y],restrict U T=some (t U) := by
    intro U hU
    rcases List.mem_cons.1 hU with rfl | hU
    · simpa only [t,ite_true] using htx
    · have he : U=Y := by simpa using hU
      subst U
      simpa [t,neq] using hty
  have rs : ∀U∈[X,Y],restrict U S=some (s U) := by
    intro U hU
    rcases List.mem_cons.1 hU with rfl | hU
    · simpa only [s,ite_true] using hsx
    · have he : U=Y := by simpa using hU
      subst U
      simpa [s,neq] using hsy
  have agr : ∀U∈[X,Y],agreement (t U) (s U) (G U)=true := by
    intro U hU
    rcases List.mem_cons.1 hU with rfl | hU
    · simpa [t,s,G] using hx
    · have he : U=Y := by simpa using hU
      subst U
      simpa [t,s,G,neq] using hy
  have h := (reverse_reconstruction T S [X,Y] G t s nt ns hpT hpS et es rt rs agr).1
  simpa [G,neq] using h

theorem original_stable_marked_merge (T S tx sx ty sy mxT mxS myT myS : Tree)
    (X Y : List Nat) (x y rho gamma m n : Nat) (FM FN : List (List Nat))
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (htx : restrict X T=some tx) (hsx : restrict X S=some sx)
    (hty : restrict Y T=some ty) (hsy : restrict Y S=some sy)
    (hMXT : marked T X y rho=some mxT) (hMXS : marked S X y rho=some mxS)
    (hMYT : marked T Y x gamma=some myT) (hMYS : marked S Y x gamma=some myS)
    (hx : x∈X) (hy : y∈Y)
    (hm : IsMinimum tx sx m) (hn : IsMinimum ty sy n)
    (hFM : agreement mxT mxS FM=true) (cFM : FM.length-1=m)
    (hFN : agreement myT myS FN=true) (cFN : FN.length-1=n) :
    ∃ G,agreement T S G=true ∧ G.length-1=m+n := by
  have subXT : X⊆leaves T := fun _ hz => (split_labels _ X Y hpT _).2 (Or.inl hz)
  have subXS : X⊆leaves S := fun _ hz => (split_labels _ X Y hpS _).2 (Or.inl hz)
  have subYT : Y⊆leaves T := fun _ hz => (split_labels _ X Y hpT _).2 (Or.inr hz)
  have subYS : Y⊆leaves S := fun _ hz => (split_labels _ X Y hpS _).2 (Or.inr hz)
  have nx := checked_block_nodup _ [X,Y] hpT X (by simp)
  have ny := checked_block_nodup _ [X,Y] hpT Y (by simp)
  have ynot : y∉X := by intro hyx;exact split_disjoint _ X Y hpT y hyx hy
  have xnot : x∉Y := split_disjoint _ X Y hpT x hx
  obtain ⟨K,FX,neK,subK,subFX,agrX,emTX,emSX,topX,lenX⟩ := stable_marked_normal_form
    T S tx sx mxT mxS X y rho m nt ns nx subXT subXS (subYT hy) (subYS hy) ynot
    htx hsx hMXT hMXS hm FM hFM cFM
  obtain ⟨L,FY,neL,subL,subFY,agrY,emTY,emSY,topY,lenY⟩ := stable_marked_normal_form
    T S ty sy myT myS Y x gamma n nt ns ny subYT subYS (subXT hx) (subXS hx) xnot
    hty hsy hMYT hMYS hn FN hFN cFN
  have hcat := two_local_reconstruction T S tx sx ty sy X Y (K::FX) (L::FY)
    nt ns hpT hpS (actual_split_embeddings T X Y nt hpT edgeT)
    (actual_split_embeddings S X Y ns hpS edgeS) htx hsx hty hsy agrX agrY
  have unionTopo := original_union_glue T S X Y K L x y nt ns hpT hpS edgeT edgeS
    subK subL neK neL hx hy topX topY
  have oneX : [x]⊆X := by
    intro z hz
    have he : z=x := by simpa using hz
    simpa [he] using hx
  have oneY : [y]⊆Y := by
    intro z hz
    have he : z=y := by simpa using hz
    simpa [he] using hy
  have h := hcat
  simp only [agreement,Bool.and_eq_true] at h
  have emb : ∀t, t=T ∨ t=S → pairwiseEmbeddings t (merged K L FX FY)=true := by
    intro t ht
    rcases ht with he | he
    · subst t
      obtain ⟨p,b,inside,sX,sY⟩ := original_split_side_guards T X Y nt hpT edgeT
      exact merge_embeddings T K L FX FY x y p b inside nt (subXT hx) (subYT hy) h.1.2 emTX emTY
        (fun a ha => sX a (selected_mono T K X subK a ha))
        (fun a ha => sY a (selected_mono T L Y subL a ha))
        (fun E hE a ha => sX a (selected_mono T E X (subFX E hE) a ha))
        (fun E hE a ha => sY a (selected_mono T E Y (subFY E hE) a ha))
        (fun a ha => sY a (selected_mono T [y] Y oneY a ha))
        (fun a ha => sX a (selected_mono T [x] X oneX a ha))
    · subst t
      obtain ⟨p,b,inside,sX,sY⟩ := original_split_side_guards S X Y ns hpS edgeS
      exact merge_embeddings S K L FX FY x y p b inside ns (subXS hx) (subYS hy) h.2 emSX emSY
        (fun a ha => sX a (selected_mono S K X subK a ha))
        (fun a ha => sY a (selected_mono S L Y subL a ha))
        (fun E hE a ha => sX a (selected_mono S E X (subFX E hE) a ha))
        (fun E hE a ha => sY a (selected_mono S E Y (subFY E hE) a ha))
        (fun a ha => sY a (selected_mono S [y] Y oneY a ha))
        (fun a ha => sX a (selected_mono S [x] X oneX a ha))
  obtain ⟨hG,hcount⟩ := original_forest_merge_of_checked_embeddings T S K L FX FY hcat unionTopo
    (emb T (Or.inl rfl)) (emb S (Or.inr rfl))
  refine ⟨merged K L FX FY,hG,?_⟩
  have pM := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty mxT mxS FM hFM)
  have pN := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty myT myS FN hFN)
  simp only [List.length_append] at hcount
  omega
end OrdinaryCommonSplit
