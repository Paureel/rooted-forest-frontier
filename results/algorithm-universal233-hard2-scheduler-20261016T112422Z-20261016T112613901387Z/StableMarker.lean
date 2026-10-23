import MarkedLift
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

/-- Equality of actual marked and unmarked minima forces every marked minimum
to carry the attachment in a non-singleton block. A singleton marker would
delete an entire block and contradict the unmarked minimum. -/
theorem stable_minimum_marker_not_singleton (T S t s mt ms : Tree)
    (X : List Nat) (y rho m : Nat)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (hn : y∉X) (hm : IsMinimum t s m)
    (F : List (List Nat)) (ha : agreement mt ms F=true) (hc : F.length-1=m) :
    [rho]∉F := by
  intro hsingle
  obtain ⟨G,hG,hGc⟩ := marked_singleton_deletion T S t s mt ms X y rho
    ht hs hmt hms F ha hn hsingle
  have low := hm.2 G hG
  have ng := Universal233.DepthOne.agreement_nonempty t s G hG
  have pg : 0<G.length := List.length_pos_iff.2 ng
  omega
end OrdinaryCommonSplit
