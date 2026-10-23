import Rule4PolynomialCuts
namespace OrdinaryDispatch.FullSourceWork

theorem rule4OutsideCap_explicit (N : Nat) :
 rule4OutsideCap N (2*N+2)=8*N^3+24*N^2+42*N+36 := by
 unfold rule4OutsideCap rule4SubtreeCap
 grind

theorem rule4PartitionCap_explicit (N : Nat) :
 rule4PartitionCap N (2*N+2)=8*N^4+40*N^3+110*N^2+126*N+61 := by
 unfold rule4PartitionCap
 rw [rule4OutsideCap_explicit]
 unfold rule4SubtreeCap
 grind

theorem rule4StateCap_explicit (N : Nat) :
 rule4StateCap N (2*N+2)=8*N^4+56*N^3+166*N^2+180*N+75 := by
 unfold rule4StateCap
 rw [rule4PartitionCap_explicit]
 grind
end OrdinaryDispatch.FullSourceWork
