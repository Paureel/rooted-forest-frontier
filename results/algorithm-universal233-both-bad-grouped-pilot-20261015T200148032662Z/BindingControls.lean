import BadGroupedPair
import GroupedControls
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
namespace Universal233.BothBadGrouped.Controls
open RMAF CoreProgram SourceCoverage PairAssembly BinaryCheap
open ForestState ForestGroups RestrictionBridge PaidQueries GroupedFullQuery

def sa : Tree := .node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4)))
def sb : Tree := .node (.node (.leaf 5) (.leaf 7)) (.node (.leaf 6) (.leaf 8))
def sc : Tree := .node (.leaf 9) (.node (.leaf 10) (.leaf 11))
def tab : Tree := .node (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 5) (.leaf 6)))
 (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 7) (.leaf 8)))
def tc : Tree := .node (.node (.leaf 9) (.leaf 10)) (.leaf 11)
def s : Tree := .node sa (.node sb sc)
def t : Tree := .node tab tc
def a : List Nat := [1,2,3,4]
-- Kept parent lists deliberately differ from the ORIGINAL output block order.
def b : List Nat := [8,7,6,5]
def c : List Nat := [11,10,9]
def edge : RMAF.Vertex × RMAF.Vertex := ([false],[false,false])
def d : List Nat := PairGeometry.descendants t edge.2

def cheap : Output := (sideOutputs s b a d 3).headD ⟨[],[]⟩
theorem original_guards : partitionCheck (leaves s) [a,b,c]=true ∧ pairwiseEmbeddings s [a,b,c]=true ∧
 restrictionAgrees s t a=false ∧ restrictionAgrees s t b=false ∧ restrictionAgrees s t c=false ∧
 PairGeometry.choose t a b=some (.edge edge) ∧
 disjointVertices (minimalVertices a t) (minimalVertices c t)=true ∧
 disjointVertices (minimalVertices b t) (minimalVertices c t)=true := by decide
example : (sideOutputs s b a d 3).map (fun o => (o.sourceCuts.length,o.partition))=
 [(3,[[5,7,6,8],[1,2],[3,4],[9,10,11]])] := by decide
example : cheap∈BothBad.outputs s a b d 6 := by decide
example : cheap.sourceCuts.length=3 ∧ cheap.partition.length=4 := by decide
example : b∉cheap.partition ∧ c∉cheap.partition := by decide
example : KeptParent.Keeps b cheap ∧ KeptParent.Keeps c cheap := by
 have facts := outputs_facts s a b c d 6 cheap original_guards.1 original_guards.2.1 (by decide)
 rcases facts.kept.1 with ka|kb
 · obtain ⟨K,hK,mem⟩ := ka
   have notA : ∀ K∈cheap.partition,¬SameMembers K a := by decide
   exact False.elim (notA K hK mem)
 · exact ⟨kb,facts.kept.2⟩

def pAB : Problem := groupProblem (some t) (OutputState.sourceForest s cheap.partition) (a++b)
def pC : Problem := groupProblem (some t) (OutputState.sourceForest s cheap.partition) c
def cAnswer : Forest := [[9],[10,11]]
def jobs : List (Job Problem Forest) := [.hard pAB,.resolved pC 1 cAnswer]
def emptyActual : Ordinary := fun _ _ _ => none
example : jobsFor t s a b c cheap=some jobs := by decide
example : pAB.sources.length=3 ∧ pC.sources.length=1 := by decide
example : badSlots jobs=2 ∧ allocated (6-cheap.sourceCuts.length) jobs=2 := by decide

theorem actual_trace : (traceFor emptyActual t s a b c 6 cheap).map Prod.snd=[2] := by
 have prep : jobsFor t s a b c cheap=some jobs := by decide
 rw [show traceFor emptyActual t s a b c 6 cheap=
   fullTrace emptyActual 3 jobs by simp [traceFor,runOutput_binding _ _ _ _ _ _ _ _ (by decide) _ prep,OutputResult.trace,fullTrace];rfl]
 cases h : callback emptyActual pAB 2 <;>
   simp [fullTrace,meterSchedule,meterRun,jobs,knownCost,pending,allocated,h]

def omitCTrace : List (Problem × Nat) := fullTrace emptyActual 3 [Job.hard pAB]
theorem omitted_trace : omitCTrace.map Prod.snd=[3] := by
 cases h : callback emptyActual pAB 3 <;>
   simp [omitCTrace,fullTrace,meterSchedule,meterRun,knownCost,pending,allocated,h]

def fullAnswer : Forest := [[5],[7],[6,8],[1,2],[3,4],[9],[10,11]]
example : agreement t s fullAnswer=true ∧ fullAnswer.length-1=6 ∧
 additionalCost (OutputState.sourceForest s cheap.partition) fullAnswer=3 := by decide
example : 6-cheap.sourceCuts.length=3 := by decide
example : (6-((traceFor emptyActual t s a b c 6 cheap).map Prod.snd).headD 99)=4 := by rw [actual_trace];decide
example : (6-(omitCTrace.map Prod.snd).headD 99)=3 := by rw [omitted_trace];decide
end Universal233.BothBadGrouped.Controls
