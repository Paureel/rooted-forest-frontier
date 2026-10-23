import LiteralMerge
namespace OrdinaryCommonSplit.Caller
open RMAF RestrictionBridge

theorem pickMerge_actual_spec (T S tx sx ty sy mxT mxS myT myS : Tree)
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
    ∃ G,pickMerge T S X Y x y rho gamma FM FN=some G ∧ agreement T S G=true ∧ G.length-1=m+n := by
  obtain ⟨H,hH,aH,cH⟩ := literal_stable_merge_candidate T S tx sx ty sy mxT mxS myT myS X Y x y rho gamma m n FM FN nt ns hpT hpS edgeT edgeS htx hsx hty hsy hMXT hMXS hMYT hMYS hx hy hm hn hFM cFM hFN cFN
  obtain ⟨G,hG⟩ := best_exists (fun G : List (List Nat)=>G.length-1) (agreement T S)
    (mergeCandidates X Y x y rho gamma FM FN) H hH aH
  obtain ⟨gmem,ga,gmin⟩ := best_spec (fun G : List (List Nat)=>G.length-1) (agreement T S)
    (mergeCandidates X Y x y rho gamma FM FN) G hG
  have upper := gmin H hH aH
  have lower := original_sum_lower T S tx sx ty sy X Y m n nt hpT edgeT htx hsx hty hsy hm hn G ga
  exact ⟨G,hG,ga,by omega⟩
end OrdinaryCommonSplit.Caller
