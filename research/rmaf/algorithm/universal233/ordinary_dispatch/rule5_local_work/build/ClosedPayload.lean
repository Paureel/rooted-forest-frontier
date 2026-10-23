import WorkBinding
import FastExact
import BuildIdentity
import CallerResources
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller
abbrev Forest := List (List Nat)
abbrev actual : Tree→Tree→Nat→Option Forest := fun T S q => OrdinaryDispatch.FastOrdinary.solve q T S

def cells (F : Forest) : Nat := F.length+F.flatten.length

theorem agreement_payload (T S : Tree) (F : Forest)
 (nd : (leaves T).Nodup) (ok : agreement T S F=true) :
 F.flatten.length=(leaves T).length ∧ F.length≤(leaves T).length ∧
 (∀x,x∈F.flatten →x∈leaves T) ∧ cells F≤2*(leaves T).length := by
 have part : partitionCheck (leaves T) F=true := by
   simp only [agreement,Bool.and_eq_true] at ok
   exact ok.1.1.1.1
 have perm := Universal233.FinalCutRecovery.checked_flatten_perm T F nd part
 have flat := perm.length_eq
 have len := Universal233.FinalCutRecovery.blocks_le_flatten F (SourceCoverage.partitionCheck_nonempty _ _ part)
 exact ⟨perm.length_eq,by omega,fun x hx => perm.mem_iff.1 hx,by unfold cells;omega⟩

/-- No hypothesis about arbitrary callback payload is used: this is the
closed, proved ordinary solver at the actual queried input. -/
theorem closed_payload (T S : Tree) (q : Nat) {F : Forest}
 (hp : DepthOne.proper T S=true) (answer : actual T S q=some F) :
 F.flatten.length=(leaves T).length ∧ F.length≤(leaves T).length ∧
 (∀x,x∈F.flatten →x∈leaves T) ∧ cells F≤2*(leaves T).length := by
 have sound := OrdinaryDispatch.FastOrdinary.query_sound
   (OrdinaryDispatch.FastOrdinary.solve_exact q T S hp) answer
 have nd : (leaves T).Nodup := by
   simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at hp
   exact hp.1.1
 exact agreement_payload T S F nd sound.1

theorem actual_trace_payload {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CoreGraph.CherryAt T i a b)
 (ad : Rule5Local.admitted T S a b=true) (q : Nat)
 {p : Tree×Tree} {r : Nat} {F : Forest}
 (mem : (p,r)∈Rule5ActualTrace.queries actual (Rule5ActualTrace.dispatchTrace actual T S a b q).calls)
 (answer : actual p.1 p.2 r=some F) :
 F.flatten.length≤(leaves T).length ∧ F.length≤(leaves T).length ∧
 cells F≤2*(leaves T).length := by
 have query := Rule5ActualTrace.dispatch_query_bounds actual ch ad q mem
 have pay := closed_payload p.1 p.2 r query.2.1 answer
 exact ⟨by omega,by omega,by omega⟩
end Universal233.Rule5LocalWork
