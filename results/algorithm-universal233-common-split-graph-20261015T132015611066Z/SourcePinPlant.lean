import MinimumIdentity
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

def commonSplitValue (m n mr ng : Nat) : Nat := if mr=m ∧ ng=n then m+n else m+n+1

/-- The global minimum is DERIVED from the four actual local minima. There is
no supplied global minimum, safe-cover, projection, gluing or equality field. -/
theorem common_split_derived_minimum (T S tx sx ty sy mxT mxS myT myS : Tree)
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
    (hr : IsMinimum mxT mxS mr) (hg : IsMinimum myT myS ng) :
    IsMinimum T S (commonSplitValue m n mr ng) := by
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
  have lower : ∀F,agreement T S F=true→m+n≤F.length-1 :=
    fun F ha => original_sum_lower T S tx sx ty sy X Y m n nt hpT edgeT htx hsx hty hsy hm hn F ha
  by_cases stable : mr=m ∧ ng=n
  · have value : commonSplitValue m n mr ng=m+n := by simp only [commonSplitValue,ite_eq_left stable]
    rw [value]
    obtain ⟨FM,hFM,cFM⟩ := hr.1
    obtain ⟨FN,hFN,cFN⟩ := hg.1
    exact ⟨original_stable_marked_merge T S tx sx ty sy mxT mxS myT myS
      X Y x y rho gamma m n FM FN nt ns hpT hpS edgeT edgeS htx hsx hty hsy hMXT hMXS hMYT hMYS
      hx hy hm hn hFM (cFM.trans stable.1) hFN (cFN.trans stable.2),lower⟩
  · have value : commonSplitValue m n mr ng=m+n+1 := by simp only [commonSplitValue,ite_eq_right stable]
    rw [value]
    obtain ⟨FX,hFX,cFX⟩ := hm.1
    obtain ⟨FY,hFY,cFY⟩ := hn.1
    have concat := two_local_reconstruction T S tx sx ty sy X Y FX FY nt ns hpT hpS
      (actual_split_embeddings T X Y nt hpT edgeT) (actual_split_embeddings S X Y ns hpS edgeS)
      htx hsx hty hsy hFX hFY
    have px := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty tx sx FX hFX)
    have py := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty ty sy FY hFY)
    refine ⟨⟨FX++FY,concat,?_⟩,?_⟩
    · simp only [List.length_append]
      omega
    · intro F ha
      have low := lower F ha
      have neq : F.length-1≠m+n := by
        intro eq
        have forced := equal_sum_marked_upper T S tx sx ty sy mxT mxS myT myS
          X Y x y rho gamma m n mr ng nt ns hpT hpS edgeT edgeS htx hsx hty hsy hMXT hMXS hMYT hMYS
          hx hy frT frS fgT fgS hm hn hr hg F ha eq
        exact stable ⟨by omega,by omega⟩
      omega
end OrdinaryCommonSplit

-- deliberate byte corruption
