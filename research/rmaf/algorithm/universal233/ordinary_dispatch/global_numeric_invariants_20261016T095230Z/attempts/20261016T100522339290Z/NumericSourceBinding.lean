import NumericActualEntries
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CherryBranching Universal233.BothBad Universal233.Hard2Overlap
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open Rule5ActualTrace OrdinaryDispatch.FastOrdinary OrdinaryDispatch.Hard2Dispatcher

def forestCallsOf : Rule5ActualTrace.Calls→List Call
 | .forestJobs jobs => jobs.map jobCall
 | .direct _ => []
 | .paidRequests jobs => jobs.flatMap currentForestCalls
 | .selectorRefused | .paidBuilderRefused => []
def directCallsOf : Rule5ActualTrace.Calls→List Query
 | .direct jobs => directQueries jobs
 | _ => []

theorem current_forest_binding (actual : GenericForest.FrontierWork.Ordinary) (j : Rule5PaidSelector.PaidRequest) :
 forestQueries actual (currentForestCalls j)=currentFrontier actual (some j.target) j.sources j.residual := by
 cases pre : ForestPretest01.pretest01 (some j.target) j.sources <;>
  simp [currentForestCalls,currentFrontier,pre,forestQueries]
 split <;> simp_all [forestQueries]

theorem calls_source_binding (actual : GenericForest.FrontierWork.Ordinary) (calls : Rule5ActualTrace.Calls) :
 queries actual calls=directCallsOf calls++forestQueries actual (forestCallsOf calls) := by
 cases calls with
 | forestJobs jobs => simp [queries,directCallsOf,forestCallsOf,forestQueries,jobCall,List.flatMap_map,Function.comp_def]
 | direct jobs => simp [queries,directCallsOf,forestCallsOf,forestQueries]
 | selectorRefused => rfl
 | paidBuilderRefused => rfl
 | paidRequests jobs =>
  simp only [queries,directCallsOf,forestCallsOf,List.nil_append]
  induction jobs with
  | nil => rfl
  | cons j jobs ih =>
   simp only [List.flatMap_cons,forestQueries,List.flatMap_append] at *
   rw [←ih,←current_forest_binding actual j]

def hard2DirectQueries (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (c : Candidate) (q : Nat) : List Query :=
 match runHard2 T S c with
 | some .disjoint =>
   let P:=pendantPartition S c.a c.b
   if P.all (restrictionAgrees T S) then []
   else if (P.filter (restrictionAgrees T S)).length=2 then directCallsOf (dispatchTrace actual T S c.a c.b q).calls
   else []
 | _ => []

theorem hard2_source_queries (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (c d : Candidate) (q : Nat) :
 (hard2Trace actual T S c d q).queries=hard2DirectQueries actual T S c q++forestQueries actual (hard2ForestCalls actual T S c q) := by
 cases sel : runHard2 T S c with
 | none => rfl
 | some out =>
  cases out with
  | disjoint =>
   by_cases good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=true
   · simp [hard2Trace,hard2DirectQueries,hard2ForestCalls,sel,good,forestQueries]
   · by_cases two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2
     · simpa [hard2Trace,hard2DirectQueries,hard2ForestCalls,sel,good,two,rule5ForestCalls,forestCallsOf] using
        calls_source_binding actual (dispatchTrace actual T S c.a c.b q).calls
     · simp [hard2Trace,hard2DirectQueries,hard2ForestCalls,sel,good,two]
  | clique v => simp [hard2Trace,hard2DirectQueries,hard2ForestCalls,sel]
  | four o v w => simp [hard2Trace,hard2DirectQueries,hard2ForestCalls,sel]
  | diagonal o v w => simp [hard2Trace,hard2DirectQueries,hard2ForestCalls,sel]
  | pair o choice => simp [hard2Trace,hard2DirectQueries,hard2ForestCalls,sel]

def ordinaryDirectQueries (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat) (T S : Tree) : List Query :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .rejected =>
   match early T S with
   | .common reverse c =>
    let p:=commonPair T S reverse c
    if (leaves p.1).length<(leaves T).length then [(p,q)] else []
   | .hard2 c _ => hard2DirectQueries (cutoff rec q) T S c q
   | _ => []
  | _ => []
 else []

/-- Exact occurrence-preserving query equality. It checks that the new forest
entry companion omits no actual ordinary callback and silently adds none. -/
theorem ordinary_source_queries (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat) (T S : Tree) :
 (ordinaryStepTrace rec q T S).queries=ordinaryDirectQueries rec q T S++forestQueries (cutoff rec q) (ordinaryForestCalls rec q T S) := by
 by_cases hp : DepthOne.proper T S=true
 · cases pre : DepthOne.pretest01 T S with
   | refused => simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,forestQueries]
   | found c => simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,forestQueries]
   | rejected =>
    cases he : early T S with
    | common reverse c =>
     simp only [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,ite_true,pre,he,forestQueries,List.flatMap_nil,List.append_nil]
     split <;> rfl
    | one reverse c => simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,he,childrenTrace,childCalls,forestQueries,jobCall,List.flatMap_map,Function.comp_def,queries]
    | high reverse c => simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,he,childrenTrace,childCalls,forestQueries,jobCall,List.flatMap_map,Function.comp_def,queries]
    | rule4Forward s => simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,he,rule4Trace]
    | rule4Reverse s => simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,he,rule4Trace]
    | hard2 c d => simpa [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,he] using hard2_source_queries (cutoff rec q) T S c d q
    | refused => simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,pre,he,forestQueries]
 · simp [ordinaryStepTrace,ordinaryDirectQueries,ordinaryForestCalls,hp,forestQueries]
end OrdinaryDispatch.GlobalNumeric
