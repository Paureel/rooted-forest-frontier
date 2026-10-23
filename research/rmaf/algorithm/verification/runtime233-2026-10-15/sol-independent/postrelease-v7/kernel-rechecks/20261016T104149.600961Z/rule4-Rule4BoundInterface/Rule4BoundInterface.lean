import Rule4PolynomialPartition
namespace OrdinaryDispatch.FullSourceWork
open RMAF Universal233 GenericForest.FrontierWork
open Universal233.Rule5PendantLocalWork

theorem rule4_nat_polynomial_combine (A B C n : Nat) :
 (1536*A+144*B+116*C+28*n+20)+
  3*((8*A+56*B+166*C+180*n+75)+2*(2*n+2)+8)+1+3*(1+2*n+4)+1+2=
 1560*A+312*B+614*C+586*n+300 := by omega

theorem rule4LocalPolynomial_explicit (N : Nat) :
 rule4LocalPolynomial N=1560*N^4+312*N^3+614*N^2+586*N+300 := by
 unfold rule4LocalPolynomial
 rw [rule4BranchCap_explicit,rule4StateCap_explicit]
 exact rule4_nat_polynomial_combine (N^4) (N^3) (N^2) N

theorem rule4SourcePolynomial_explicit (N Q : Nat) :
 rule4SourcePolynomial N Q=
  1560*N^4+312*N^3+614*N^2+586*N+300+48*(2^50*(N+Q+2)^8) := by
 simp only [rule4SourcePolynomial,rule4LocalPolynomial_explicit]

/-- Actual cutoff caller requested by the consuming ordinary recursion.
Choice's original admission already includes nodup and common labels. -/
theorem rule4Source_cutoff_bound {T S : Tree} (s : Rule4.Choice T S) (q N Q : Nat)
 (size : (leaves T).length≤N) (budget : q≤Q) :
 ((rule4Source (OrdinaryDispatch.FastOrdinary.cutoff OrdinaryDispatch.FastOrdinary.solve q)
   (fun _ _ _=>0) s q).work:Rat)≤
 (1560*N^4+312*N^3+614*N^2+586*N+300+48*(2^50*(N+Q+2)^8):Nat)*(233/100:Rat)^q := by
 simpa only [rule4SourcePolynomial_explicit,Rule5ActualTrace.base] using
  rule4Source_bound (OrdinaryDispatch.FastOrdinary.cutoff OrdinaryDispatch.FastOrdinary.solve q) s q N Q size budget
end OrdinaryDispatch.FullSourceWork
