import GroupInterface
import ForestPretestControls
namespace Universal233.GroupedFullQuery.Controls
open RMAF ForestState ForestGroups RestrictionBridge PaidQueries

def emptyActual : Ordinary := fun _ _ _ => none
example : prepareOne ⟨[],none,[]⟩=some (.resolved ⟨[],none,[]⟩ 0 []) := by decide
example : prepareOne ⟨[9],some (.leaf 9),[.leaf 9]⟩=
 some (.resolved ⟨[9],some (.leaf 9),[.leaf 9]⟩ 0 [[9]]) := by decide
example : prepareOne ⟨[],none,[.leaf 9]⟩=none := by decide

def overlap : Problem := ⟨[0,1,2,3],some ForestPretest01.Controls.t,ForestPretest01.Controls.ss⟩
example : prepareOne overlap=some (.resolved overlap 1 ForestPretest01.Controls.witness) := by decide

def sa : Tree := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def sb : Tree := .node (.leaf 3) (.node (.leaf 4) (.leaf 5))
def sc : Tree := .node (.leaf 6) (.node (.leaf 7) (.leaf 8))
def tab : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 3) (.leaf 4))) (.node (.leaf 2) (.leaf 5))
def tc : Tree := .node (.node (.leaf 6) (.leaf 7)) (.leaf 8)
def s : Tree := .node sa (.node sb sc)
def t : Tree := .node tab tc
def a : List Nat := [0,1,2]
def b : List Nat := [3,4,5]
def c : List Nat := [6,7,8]
def pAB : Problem := ⟨a++b,some tab,[sa,sb]⟩
def pC : Problem := ⟨c,some tc,[sc]⟩
def cAnswer : Forest := [[6],[7,8]]
def jobs : List (Job Problem Forest) := [.hard pAB,.resolved pC 1 cAnswer]

theorem actual_original_guards : partitionCheck (leaves s) [a,b,c]=true ∧
 pairwiseEmbeddings s [a,b,c]=true ∧ restrictionAgrees t s a=false ∧
 restrictionAgrees t s b=false ∧ restrictionAgrees t s c=false ∧
 disjointVertices (minimalVertices a t) (minimalVertices c t)=true ∧
 disjointVertices (minimalVertices b t) (minimalVertices c t)=true ∧
 disjointVertices (minimalVertices a t) (minimalVertices b t)=false := by decide
example : (match PairGeometry.choose t a b with | some (.edge _) => true | _ => false)=true := by decide

theorem actual_group_payload : groupProblems (some t) (OutputState.sourceForest s [a,b,c]) [a++b,c]=[pAB,pC] := by decide
example : pAB.sources.length=2 ∧ pC.sources.length=1 := by decide
example : prepareOne pAB=some (.hard pAB) := by decide
example : prepareOne pC=some (.resolved pC 1 cAnswer) := by decide
example : prepare (groupProblems (some t) (OutputState.sourceForest s [a,b,c]) [a++b,c])=some jobs := by decide
example : badSlots jobs=2 ∧ knownCost jobs=1 ∧ pending jobs=1 ∧ allocated 3 jobs=2 := by decide

example : (fullTrace emptyActual 3 jobs).map Prod.snd=[2] := by
 cases h : callback emptyActual pAB 2 <;>
   simp [fullTrace,meterSchedule,meterRun,jobs,knownCost,pending,allocated,h]

-- Synthetic callbacks here test scheduler plumbing, with no correctness-IH claim.
def planted (_ : Problem) (_ : Nat) : Option (Nat × Forest) := some (2,[[99]])
def twoHard : List (Job Problem Forest) := [.hard pAB,.hard pAB]
example : allocated 5 twoHard=3 ∧ (schedule planted 5 twoHard).calls=[3,3] := by decide
example : allocated 3 ([.hard pAB] : List (Job Problem Forest))=3 := by decide
example : (schedule planted 3 jobs).answers=some [(2,[[99]]),(1,cAnswer)] := by decide
example : (schedule planted 3 ([.hard pAB] : List (Job Problem Forest))).answers=some [(2,[[99]])] := by decide
example : actualQueryMass 2 5 (schedule planted 5 twoHard).calls=(1/2 : Rat) := by decide
example : actualQueryMass 2 3 (schedule planted 3 ([.hard pAB] : List (Job Problem Forest))).calls=1 := by decide
end Universal233.GroupedFullQuery.Controls
