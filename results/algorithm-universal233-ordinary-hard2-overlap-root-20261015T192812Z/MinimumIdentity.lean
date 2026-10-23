import CountOriginal
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem OriginalSplit.swap (T : Tree) (X Y : List Nat) (h : OriginalSplit T X Y) : OriginalSplit T Y X := by
  obtain ⟨p,u,ne,hp,side⟩ := h
  exact ⟨p,u,ne,hp,side.elim Or.inr Or.inl⟩

theorem equal_sum_marked_upper (T S tx sx ty sy mxT mxS myT myS : Tree)
    (X Y : List Nat) (x y rho gamma m n mr ng : Nat)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (htx : restrict X T=some tx) (hsx : restrict X S=some sx)
    (hty : restrict Y T=some ty) (hsy : restrict Y S=some sy)
    (hMXT : marked T X y rho=some mxT) (hMXS : marked S X y rho=some mxS)
    (hMYT : marked T Y x gamma=some myT) (hMYS : marked S Y x gamma=some myS)
    (hx : x∈X) (hy : y∈Y)
    (frT : rho∉leaves T) (frS : rho∉leaves S)
    (fgT : gamma∉leaves T) (fgS : gamma∉leaves S)
    (hm : IsMinimum tx sx m) (hn : IsMinimum ty sy n)
    (hr : IsMinimum mxT mxS mr) (hg : IsMinimum myT myS ng)
    (F : List (List Nat)) (ha : agreement T S F=true) (hc : F.length-1=m+n) : mr≤m ∧ ng≤n := by
  have gx := (agreement_clip T S tx sx X F htx hsx ha).1
  have gy := (agreement_clip T S ty sy Y F hty hsy ha).1
  have lx := hm.2 _ gx
  have ly := hn.2 _ gy
  have px := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty tx sx _ gx)
  have py := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty ty sy _ gy)
  have count := actual_split_clip_bound T S X Y F nt hpT edgeT ha
  have cx : (clip X F).length-1=m := by omega
  have cy : (clip Y F).length-1=n := by omega
  obtain ⟨B,hB,nX,nY⟩ := equal_sum_has_crossing T S tx sx ty sy X Y m n
    hpT htx hsx hty hsy hm hn F ha hc
  obtain ⟨G,hG,hGc⟩ := arbitrary_original_marked_projection T S mxT mxS X Y B F y rho
    nt ns hpT hpS edgeT edgeS hB nX nY hy frT frS hMXT hMXS ha
  have hpT' := BinaryExchange.partition_perm _ [X,Y] [Y,X] (List.Perm.swap X Y []).symm hpT
  have hpS' := BinaryExchange.partition_perm _ [X,Y] [Y,X] (List.Perm.swap X Y []).symm hpS
  obtain ⟨H,hH,hHc⟩ := arbitrary_original_marked_projection T S myT myS Y X B F x gamma
    nt ns hpT' hpS' (edgeT.swap T X Y) (edgeS.swap S X Y) hB nY nX hx fgT fgS hMYT hMYS ha
  have ur := hr.2 G hG
  have ug := hg.2 H hH
  omega

/-- Exact ordinary-cut common-split identity. Local minima are witnessed
actual AF minima; the theorem derives every global projection and merge from
actual original cuts, with either rooted orientation and explicit markers. -/
theorem common_split_minimum_identity (T S tx sx ty sy mxT mxS myT myS : Tree)
    (X Y : List Nat) (x y rho gamma m n mr ng g : Nat)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (hpT : partitionCheck (leaves T) [X,Y]=true) (hpS : partitionCheck (leaves S) [X,Y]=true)
    (edgeT : OriginalSplit T X Y) (edgeS : OriginalSplit S X Y)
    (htx : restrict X T=some tx) (hsx : restrict X S=some sx)
    (hty : restrict Y T=some ty) (hsy : restrict Y S=some sy)
    (hMXT : marked T X y rho=some mxT) (hMXS : marked S X y rho=some mxS)
    (hMYT : marked T Y x gamma=some myT) (hMYS : marked S Y x gamma=some myS)
    (hx : x∈X) (hy : y∈Y)
    (frT : rho∉leaves T) (frS : rho∉leaves S)
    (fgT : gamma∉leaves T) (fgS : gamma∉leaves S)
    (hm : IsMinimum tx sx m) (hn : IsMinimum ty sy n)
    (hr : IsMinimum mxT mxS mr) (hg : IsMinimum myT myS ng) (hall : IsMinimum T S g) :
    g=if mr=m ∧ ng=n then m+n else m+n+1 := by
  have sXT : X⊆leaves T := fun _ hz => (split_labels _ X Y hpT _).2 (Or.inl hz)
  have sXS : X⊆leaves S := fun _ hz => (split_labels _ X Y hpS _).2 (Or.inl hz)
  have sYT : Y⊆leaves T := fun _ hz => (split_labels _ X Y hpT _).2 (Or.inr hz)
  have sYS : Y⊆leaves S := fun _ hz => (split_labels _ X Y hpS _).2 (Or.inr hz)
  have nx := checked_block_nodup _ [X,Y] hpT X (by simp)
  have ny := checked_block_nodup _ [X,Y] hpT Y (by simp)
  have yn : y∉X := by intro h;exact split_disjoint _ X Y hpT y h hy
  have xn := split_disjoint _ X Y hpT x hx
  have bx := marked_minimum_bounds T S tx sx mxT mxS X y rho m mr nt ns nx
    sXT sXS (sYT hy) (sYS hy) yn htx hsx hMXT hMXS hm hr
  have byb := marked_minimum_bounds T S ty sy myT myS Y x gamma n ng nt ns ny
    sYT sYS (sXT hx) (sXS hx) xn hty hsy hMYT hMYS hn hg
  obtain ⟨F,hF,cF⟩ := hall.1
  have lower := original_sum_lower T S tx sx ty sy X Y m n nt hpT edgeT
    htx hsx hty hsy hm hn F hF
  obtain ⟨FX,hFX,cFX⟩ := hm.1
  obtain ⟨FY,hFY,cFY⟩ := hn.1
  have concat := two_local_reconstruction T S tx sx ty sy X Y FX FY nt ns hpT hpS
    (actual_split_embeddings T X Y nt hpT edgeT) (actual_split_embeddings S X Y ns hpS edgeS)
    htx hsx hty hsy hFX hFY
  have upper := hall.2 (FX++FY) concat
  have pX := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty tx sx FX hFX)
  have pY := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty ty sy FY hFY)
  simp only [List.length_append] at upper
  by_cases stable : mr=m ∧ ng=n
  · obtain ⟨FM,hFM,cFM⟩ := hr.1
    obtain ⟨FN,hFN,cFN⟩ := hg.1
    obtain ⟨G,hG,cG⟩ := original_stable_marked_merge T S tx sx ty sy mxT mxS myT myS
      X Y x y rho gamma m n FM FN nt ns hpT hpS edgeT edgeS htx hsx hty hsy hMXT hMXS hMYT hMYS
      hx hy hm hn hFM (cFM.trans stable.1) hFN (cFN.trans stable.2)
    have bound := hall.2 G hG
    rw [if_pos stable]
    omega
  · have neq : g≠m+n := by
      intro eq
      have forced := equal_sum_marked_upper T S tx sx ty sy mxT mxS myT myS
        X Y x y rho gamma m n mr ng nt ns hpT hpS edgeT edgeS htx hsx hty hsy hMXT hMXS hMYT hMYS
        hx hy frT frS fgT fgS hm hn hr hg F hF (cF.trans eq)
      exact stable ⟨by omega,by omega⟩
    rw [if_neg stable]
    omega
end OrdinaryCommonSplit
