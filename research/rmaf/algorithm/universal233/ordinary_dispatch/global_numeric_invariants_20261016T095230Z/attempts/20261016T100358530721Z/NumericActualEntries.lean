import NumericEntries
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CherryBranching Universal233.BothBad Universal233.Hard2Overlap
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.Hard2Dispatcher

/-- Source-order forest-entry companion of the literal hard2 body. Direct
common jobs remain ordinary trace edges. No answer-based deduplication occurs. -/
def hard2ForestCalls (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (c : Candidate) (q : Nat) : List Call :=
 match runHard2 T S c with
 | none => []
 | some .disjoint =>
   let P:=pendantPartition S c.a c.b
   if P.all (restrictionAgrees T S) then []
   else if (P.filter (restrictionAgrees T S)).length=2 then rule5ForestCalls actual T S c.a c.b q
   else (Hard2Trace.disjointExecution actual T S c.a c.b q).calls
 | some out => (Hard2Combine.combine actual T S c.a c.b q (paidCase actual T S c q out)).calls

theorem hard2_forest_entry_caps (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree} {c d : Candidate}
 (q : Nat) (hp : DepthOne.proper T S=true)
 (forward : CherryBranching.select T S=some (.hard2,c)) (reverse : CherryBranching.select S T=some (.hard2,d))
 (noT : Rule4.select T S=none) (noS : Rule4.select S T=none) (N M : Nat)
 (sz : (leaves T).length≤N ∧ (leaves S).length≤N) (cap : PairCap M T S)
 (call : Call) (mem : call∈hard2ForestCalls actual T S c q) : ForestCaps N M q call := by
 cases selected : runHard2 T S c with
 | none => simp [hard2ForestCalls,selected] at mem
 | some out =>
  cases out with
  | disjoint =>
   by_cases good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=true
   · simp [hard2ForestCalls,selected,good] at mem
   · by_cases two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2
     · have ad:=(actual_disjoint_admission_iff hp forward reverse noT noS selected).2 two
       apply rule5_entry_caps actual (selected_actual forward).1 ad q N M sz cap call
       simpa [hard2ForestCalls,selected,good,two] using mem
     · apply disjoint_entry_caps actual q hp forward N M sz.1 cap.1 call
       simpa [hard2ForestCalls,selected,good,two] using mem
  | clique v => apply combined_entry_caps actual hp forward selected N M sz.1 cap.1 call;simpa [hard2ForestCalls,selected] using mem
  | four o v w => apply combined_entry_caps actual hp forward selected N M sz.1 cap.1 call;simpa [hard2ForestCalls,selected] using mem
  | diagonal o v w => apply combined_entry_caps actual hp forward selected N M sz.1 cap.1 call;simpa [hard2ForestCalls,selected] using mem
  | pair o choice => apply combined_entry_caps actual hp forward selected N M sz.1 cap.1 call;simpa [hard2ForestCalls,selected] using mem

/-- Literal external forest calls at one ordinary source invocation. Refusal,
base answers and common contraction make no forest call. This is a read-only
source companion, and does not replace or change the frozen algorithm. -/
def ordinaryForestCalls (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat) (T S : Tree) : List Call :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .refused | .found _ => []
  | .rejected =>
   let paid:=cutoff rec q
   match early T S with
   | .common _ _ => []
   | .one reverse c => let p:=Oriented reverse T S;childCalls p.1 q [pendantChild p.2 c.a c.b]
   | .high reverse c => let p:=Oriented reverse T S;childCalls p.1 q (branches p.2 c.a c.b)
   | .rule4Forward s => rule4Calls s q
   | .rule4Reverse s => rule4Calls s q
   | .hard2 c _ => hard2ForestCalls paid T S c q
   | .refused => []
 else []

theorem ordinary_forest_entry_caps (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat)
 {T S : Tree} (hp : DepthOne.proper T S=true) (N M : Nat)
 (sz : (leaves T).length≤N ∧ (leaves S).length≤N) (cap : PairCap M T S)
 (call : Call) (mem : call∈ordinaryForestCalls rec q T S) : ForestCaps N M q call := by
 simp only [ordinaryForestCalls,hp,ite_true] at mem
 cases pre : DepthOne.pretest01 T S with
 | refused => simp [pre] at mem
 | found c => simp [pre] at mem
 | rejected =>
  simp only [pre] at mem
  cases he : early T S with
  | common reverse c => simp [he] at mem
  | one reverse c =>
   have sel : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.one,c) := by
    simpa only [he,EarlySound] using early_sound T S
   apply child_entry_caps _ q N M _ _ _ (oriented_cap cap reverse).1 call (by simpa only [he] using mem)
   · intro c hc
     have eq : c=pendantChild (Oriented reverse T S).2 _ _ := by simpa using hc
     subst c
     exact selected_children_proper (oriented_proper hp reverse) sel _ (by simp [branches])
   · rw [oriented_size hp reverse];exact sz.1
  | high reverse c =>
   have sel : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.high,c) := by
    simpa only [he,EarlySound] using early_sound T S
   apply child_entry_caps _ q N M _
    (fun c hc=>selected_children_proper (oriented_proper hp reverse) sel c hc) _ (oriented_cap cap reverse).1 call
    (by simpa only [he] using mem)
   rw [oriented_size hp reverse];exact sz.1
  | rule4Forward s => exact rule4_entry_caps s q N M sz.1 cap call (by simpa only [he] using mem)
  | rule4Reverse s => exact rule4_entry_caps s q N M sz.2 ⟨cap.2,cap.1⟩ call (by simpa only [he] using mem)
  | hard2 c d =>
   have facts : select T S=some (.hard2,c) ∧ select S T=some (.hard2,d) ∧
       Rule4.select T S=none ∧ Rule4.select S T=none := by
    simpa only [he,EarlySound] using early_sound T S
   exact hard2_forest_entry_caps (cutoff rec q) q hp facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 N M sz cap call (by simpa only [he] using mem)
  | refused => simp [he] at mem

/-- Original-input forest-entry caps at every actually reachable ordinary
source invocation. Q is independent of every reduced leaf count. -/
theorem reachable_forest_entry_caps (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) (call : Call)
 (mem : call∈ordinaryForestCalls rec q T S) : ForestCaps N (M+2*(Q+N)) Q call := by
 have h:=reachable_invariant rec Q N M T0 S0 hp0 size0 cap0 reach
 have global:=reachable_uniform_cap rec Q N M T0 S0 hp0 size0 cap0 reach
 have caps:=ordinary_forest_entry_caps rec q h.1 N _ ⟨h.2.2.1,h.2.2.2.1⟩ global call mem
 exact ⟨caps.1,caps.2.1,by omega,caps.2.2.2⟩

/-- All actual forest replacement descendants inherit original caps and have
at most Q paid forest edges after entry. -/
theorem reachable_forest_desc_caps (rec : Nat→Tree→Tree→Option CommonForest) (Q N M : Nat) (T0 S0 : Tree)
 (hp0 : DepthOne.proper T0 S0=true) (size0 : (leaves T0).length≤N) (cap0 : PairCap M T0 S0)
 {d T S q} (reach : Reach rec Q T0 S0 d T S q) (call : Call)
 (mem : call∈ordinaryForestCalls rec q T S) {e ss r}
 (path : ForestDesc call.target call.sources call.budget e ss r) :
 proper call.target ss=true ∧ e+r≤Q ∧ GenericForest.targetNodes call.target≤2*N ∧
 GenericForest.sourceNodes ss≤2*N ∧ ss.length≤2*N ∧ (ss.map leaves).flatten.length≤N ∧
 (∀s,s∈ss→Universal233.CoreWork.treeNodes s≤2*N ∧ (leaves s).length≤N ∧
 TreeCap (M+2*(Q+N)) s ∧ ∀v,CoreGraph.Valid s v→v.length≤2*N) := by
 have caps:=reachable_forest_entry_caps rec Q N M T0 S0 hp0 size0 cap0 reach call mem
 have desc:=forest_desc_invariant call.target call.sources call.budget N _ caps.1 caps.2.1 caps.2.2.2 path
 exact ⟨desc.1,by omega,desc.2.2⟩
end OrdinaryDispatch.GlobalNumeric
