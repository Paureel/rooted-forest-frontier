import EarlyFacts
namespace OrdinaryDispatch.FastOrdinary
open RMAF ForestState Universal233 Universal233.CherryBranching

/-- External k counts components. The k=0 guard precedes every query; the
ordinary solver uses q=k-1. Original cut recovery is invoked exactly once on
the final returned forest, never during recursive dispatch. -/
def externalWith (query : Nat→Tree→Tree→Option CommonForest) (T S : Tree) (k : Nat) : Option CoreProgram.Output :=
 if k=0 then none else (query (k-1) T S).bind (FinalCutRecovery.recover S)

def ExternalExact (T S : Tree) (k : Nat) : Option CoreProgram.Output→Prop
 | none => ∀F,agreement T S F=true → k<F.length
 | some o => CutRealization.RealizedOutput S o ∧ agreement T S o.partition=true ∧
   o.sourceCuts.length+1=o.partition.length ∧ o.partition.length≤k ∧
   ∀F,agreement T S F=true → o.partition.length≤F.length

theorem original_positive {T S : Tree} {F : CommonForest} (ha : agreement T S F=true) : 0<F.length :=
 List.length_pos_iff.2 (DepthOne.agreement_nonempty T S F ha)

theorem externalWith_zero (query : Nat→Tree→Tree→Option CommonForest) (T S : Tree) :
 externalWith query T S 0=none := rfl

theorem externalWith_exact (query : Nat→Tree→Tree→Option CommonForest) (T S : Tree) (k : Nat)
 (hp : DepthOne.proper T S=true)
 (ex : 0<k → QueryExact T S (k-1) (query (k-1) T S)) :
 ExternalExact T S k (externalWith query T S k) := by
 by_cases zero : k=0
 · simp only [externalWith,zero,ite_true,ExternalExact]
   intro F ha
   exact original_positive ha
 · have pos : 0<k := by omega
   have exactness := ex pos
   simp only [externalWith,zero,ite_false]
   cases answer : query (k-1) T S with
   | none =>
     rw [answer] at exactness
     simp only [Option.bind_none,ExternalExact]
     intro F ha
     have low := exactness F ha
     omega
   | some F =>
     rw [answer] at exactness
     have af := exactness.1
     have budget := exactness.2.1
     have fpos := original_positive af
     have ns := ((DepthOne.proper_iff T S).1 hp).2.1
     obtain ⟨o,recovered,oaf,cuts,parts,realized,perm⟩ := FinalCutRecovery.recover_original_agreement T S F ns af
     simp only [Option.bind_some,recovered,ExternalExact]
     exact ⟨realized,oaf,by omega,by omega,fun G hG => parts ▸ exactness.2.2 G hG⟩

theorem externalWith_edges (query : Nat→Tree→Tree→Option CommonForest) (T S : Tree) (k : Nat)
 {o : CoreProgram.Output} (returned : externalWith query T S k=some o) :
 o.sourceCuts.Nodup ∧ ∀e,e∈o.sourceCuts → CoreGraph.Valid S e ∧ e≠[] := by
 unfold externalWith at returned
 split at returned
 · contradiction
 · obtain ⟨F,_,recover⟩ := Option.bind_eq_some_iff.1 returned
   exact FinalCutRecovery.recover_edges S F o recover
end OrdinaryDispatch.FastOrdinary
