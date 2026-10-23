import PickMerge
namespace OrdinaryCommonSplit.Caller
open RMAF RestrictionBridge

/-- Only literal input guards and lookup equations. No coverage, minimum,
reconstruction, desired saving or running-time conclusion is a field. The
source Case3.1 caller still has to construct this setup from its geometry. -/
structure Setup where
  T : Tree
  S : Tree
  tx : Tree
  sx : Tree
  ty : Tree
  sy : Tree
  mxT : Tree
  mxS : Tree
  myT : Tree
  myS : Tree
  X : List Nat
  Y : List Nat
  x : Nat
  y : Nat
  rho : Nat
  gamma : Nat
  nt : (leaves T).Nodup
  ns : (leaves S).Nodup
  hpT : partitionCheck (leaves T) [X,Y]=true
  hpS : partitionCheck (leaves S) [X,Y]=true
  edgeT : OriginalSplit T X Y
  edgeS : OriginalSplit S X Y
  htx : restrict X T=some tx
  hsx : restrict X S=some sx
  hty : restrict Y T=some ty
  hsy : restrict Y S=some sy
  hMXT : marked T X y rho=some mxT
  hMXS : marked S X y rho=some mxS
  hMYT : marked T Y x gamma=some myT
  hMYS : marked S Y x gamma=some myS
  hx : x∈X
  hy : y∈Y
  frT : rho∉leaves T
  frS : rho∉leaves S
  fgT : gamma∉leaves T
  fgS : gamma∉leaves S

def reconstruct (d : Setup) (FX FY FM FN : List (List Nat)) : Option (List (List Nat)) :=
  if FM.length-1=FX.length-1 ∧ FN.length-1=FY.length-1 then
    pickMerge d.T d.S d.X d.Y d.x d.y d.rho d.gamma FM FN
  else some (FX++FY)

theorem setup_minimum (d : Setup) (m n mr ng : Nat)
    (hm : IsMinimum d.tx d.sx m) (hn : IsMinimum d.ty d.sy n)
    (hr : IsMinimum d.mxT d.mxS mr) (hg : IsMinimum d.myT d.myS ng) :
    IsMinimum d.T d.S (commonSplitValue m n mr ng) :=
  common_split_derived_minimum d.T d.S d.tx d.sx d.ty d.sy d.mxT d.mxS d.myT d.myS
    d.X d.Y d.x d.y d.rho d.gamma m n mr ng d.nt d.ns d.hpT d.hpS d.edgeT d.edgeS
    d.htx d.hsx d.hty d.hsy d.hMXT d.hMXS d.hMYT d.hMYS d.hx d.hy
    d.frT d.frS d.fgT d.fgS hm hn hr hg

theorem reconstruct_actual_spec (d : Setup) (FX FY FM FN : List (List Nat))
    (hFX : agreement d.tx d.sx FX=true) (hFY : agreement d.ty d.sy FY=true)
    (hFM : agreement d.mxT d.mxS FM=true) (hFN : agreement d.myT d.myS FN=true)
    (hm : IsMinimum d.tx d.sx (FX.length-1)) (hn : IsMinimum d.ty d.sy (FY.length-1))
    (hr : IsMinimum d.mxT d.mxS (FM.length-1)) (hg : IsMinimum d.myT d.myS (FN.length-1)) :
    ∃ G,reconstruct d FX FY FM FN=some G ∧ agreement d.T d.S G=true ∧
      G.length-1=commonSplitValue (FX.length-1) (FY.length-1) (FM.length-1) (FN.length-1) ∧
      ∀H,agreement d.T d.S H=true→G.length-1≤H.length-1 := by
  have minimum := setup_minimum d _ _ _ _ hm hn hr hg
  by_cases stable : FM.length-1=FX.length-1 ∧ FN.length-1=FY.length-1
  · obtain ⟨G,hG,aG,cG⟩ := pickMerge_actual_spec d.T d.S d.tx d.sx d.ty d.sy d.mxT d.mxS d.myT d.myS
      d.X d.Y d.x d.y d.rho d.gamma (FX.length-1) (FY.length-1) FM FN d.nt d.ns
      d.hpT d.hpS d.edgeT d.edgeS d.htx d.hsx d.hty d.hsy d.hMXT d.hMXS d.hMYT d.hMYS
      d.hx d.hy hm hn hFM stable.1 hFN stable.2
    have value : commonSplitValue (FX.length-1) (FY.length-1) (FM.length-1) (FN.length-1)=
        (FX.length-1)+(FY.length-1) := by simp [commonSplitValue,stable]
    refine ⟨G,by simpa only [reconstruct,if_pos stable] using hG,aG,cG.trans value.symm,?_⟩
    intro H aH
    rw [cG,←value]
    exact minimum.2 H aH
  · have aG := two_local_reconstruction d.T d.S d.tx d.sx d.ty d.sy d.X d.Y FX FY
      d.nt d.ns d.hpT d.hpS (actual_split_embeddings d.T d.X d.Y d.nt d.hpT d.edgeT)
      (actual_split_embeddings d.S d.X d.Y d.ns d.hpS d.edgeS) d.htx d.hsx d.hty d.hsy hFX hFY
    have px := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty d.tx d.sx FX hFX)
    have py := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty d.ty d.sy FY hFY)
    have value : (FX++FY).length-1=
        commonSplitValue (FX.length-1) (FY.length-1) (FM.length-1) (FN.length-1) := by
      simp only [commonSplitValue,if_neg stable,List.length_append]
      omega
    refine ⟨FX++FY,by simp only [reconstruct,if_neg stable],aG,value,?_⟩
    intro H aH
    rw [value]
    exact minimum.2 H aH
end OrdinaryCommonSplit.Caller
