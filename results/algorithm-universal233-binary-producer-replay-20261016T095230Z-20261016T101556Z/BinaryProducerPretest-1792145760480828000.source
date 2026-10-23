import BinaryProducerAgreement
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork

theorem containsLabel_value (x : Bits) (L : Block) :
 (containsLabel x L).value=(blockValue L).contains (decode x) := by
 let C:=(prepareCapacity [x] [L]).value
 have r:=prepareCapacity_spec [x] [L]
 have p:=(containsLabel_projects C.length x L (r.1 x (by simp)) (r.2.1 L (by simp))).1
 simpa [Universal233.WholeSourceWork.meterContains_value,labelValue] using p

def subtreeBits : BinaryProvider.Tree→RMAF.Vertex→Charged (Option BinaryProvider.Tree)
 | t,[]=>⟨some t,4⟩
 | .leaf _,_::_=>⟨none,4⟩
 | .node l r,b::bs=>let s:=subtreeBits (if b then r else l) bs;⟨s.value,s.work+4⟩
@[simp] theorem subtreeBits_value (S : BinaryProvider.Tree) (p : RMAF.Vertex) :
 targetValue (subtreeBits S p).value=Universal233.CoreGraph.subtree (treeValue S) p := by
 induction p generalizing S with
 | nil=>rfl
 | cons b bs ih=>
  cases S <;> cases b <;> simp [subtreeBits,treeValue,Universal233.CoreGraph.subtree,targetValue]
  all_goals exact ih _

def subtreeLeavesBits (S : BinaryProvider.Tree) (p : RMAF.Vertex) : Charged Block :=
 let s:=subtreeBits S p
 match s.value with
 | none=>⟨[],s.work+4⟩
 | some u=>let l:=leavesCopy u;⟨l.value,s.work+l.work+4⟩
theorem subtreeLeavesBits_value (S : BinaryProvider.Tree) (p : RMAF.Vertex) :
 blockValue (subtreeLeavesBits S p).value=Universal233.DepthOne.subtreeLabels (treeValue S) p := by
 have h:=subtreeBits_value S p
 cases hs : (subtreeBits S p).value <;> simp only [hs,targetValue,Option.map_none,Option.map_some] at h
 all_goals simp [subtreeLeavesBits,hs,Universal233.DepthOne.subtreeLabels,←h,←leaves_projection,blockValue]

def excludeLabels (U : Block) : Block→Charged Block
 | []=>⟨[],1⟩
 | x::xs=>let c:=containsLabel x U;let r:=excludeLabels U xs
           ⟨if c.value then r.value else x::r.value,c.work+r.work+6⟩
theorem excludeLabels_value (U L : Block) :
 blockValue (excludeLabels U L).value=(blockValue L).filter (fun x=>!(blockValue U).contains x) := by
 induction L with
 | nil=>rfl
 | cons x xs ih=>simp only [excludeLabels,containsLabel_value,blockValue,List.map_cons,List.filter_cons,labelValue] at *;split <;> simp_all [labelValue]

def forestBits (S : BinaryProvider.Tree) : Option RMAF.Vertex→Charged BinaryProvider.Forest
 | none=>let a:=leavesCopy S;⟨[a.value],a.work+4⟩
 | some p=>let a:=subtreeLeavesBits S p;let b:=leavesCopy S;let c:=excludeLabels a.value b.value
            ⟨[a.value,c.value],a.work+b.work+c.work+8⟩
@[simp] theorem forestBits_value (S : BinaryProvider.Tree) (c : Option RMAF.Vertex) :
 forestValue (forestBits S c).value=Universal233.DepthOne.forest (treeValue S) c := by
 cases c <;> simp [forestBits,Universal233.DepthOne.forest,Universal233.DepthOne.complement,forestValue,
  leavesCopy_value,leaves_projection,subtreeLeavesBits_value,excludeLabels_value]

def verticesBits : BinaryProvider.Tree→Charged Addresses
 | .leaf _=>⟨[[]],4⟩
 | .node l r=>let a:=verticesBits l;let b:=verticesBits r;let j:=joinAddresses a.value b.value
               ⟨j.value,a.work+b.work+j.work+4⟩
@[simp] theorem verticesBits_value (S : BinaryProvider.Tree) :
 (verticesBits S).value=Universal233.DepthOne.vertices (treeValue S) := by
 induction S <;> simp_all [verticesBits,treeValue,Universal233.DepthOne.vertices,RMAF.prependSide]
def edgesBits : BinaryProvider.Tree→Charged Addresses
 | .leaf _=>⟨[],1⟩
 | .node l r=>let a:=verticesBits l;let b:=verticesBits r
               let x:=prependAddresses false a.value;let y:=prependAddresses true b.value
               let j:=appendSpine x.value y.value
               ⟨j.value,a.work+b.work+x.work+y.work+j.work+4⟩
@[simp] theorem edgesBits_value (S : BinaryProvider.Tree) :
 (edgesBits S).value=Universal233.DepthOne.edges (treeValue S) := by
 cases S <;> simp [edgesBits,treeValue,Universal233.DepthOne.edges,RMAF.prependSide]
def someCuts : Addresses→Charged (List (Option RMAF.Vertex))
 | []=>⟨[],1⟩
 | p::ps=>let r:=someCuts ps;⟨some p::r.value,r.work+4⟩
@[simp] theorem someCuts_value (ps : Addresses) : (someCuts ps).value=ps.map some := by
 induction ps <;> simp_all [someCuts]
def candidatesBits (S : BinaryProvider.Tree) : Charged (List (Option RMAF.Vertex)):=
 let e:=edgesBits S;let c:=someCuts e.value;⟨none::c.value,e.work+c.work+4⟩
@[simp] theorem candidatesBits_value (S : BinaryProvider.Tree) :
 (candidatesBits S).value=Universal233.DepthOne.candidates (treeValue S) := by simp [candidatesBits,Universal233.DepthOne.candidates]

def cutLe : Option RMAF.Vertex→Option RMAF.Vertex→Bool
 | some _,none=>false | _,_=>true
@[simp] theorem cutLe_value (a b : Option RMAF.Vertex) :
 cutLe a b=decide (Universal233.DepthOne.cutCost a≤Universal233.DepthOne.cutCost b) := by
 cases a <;> cases b <;> simp [cutLe,Universal233.DepthOne.cutCost]

def cutValid (T S : BinaryProvider.Tree) (c : Option RMAF.Vertex) : Charged Bool:=
 let f:=forestBits S c;let a:=agreementPair T S f.value;⟨a.value,f.work+a.work+4⟩
@[simp] theorem cutValid_value (T S : BinaryProvider.Tree) (c : Option RMAF.Vertex) :
 (cutValid T S c).value=RMAF.agreement (treeValue T) (treeValue S) (Universal233.DepthOne.forest (treeValue S) c) := by
 simp [cutValid,agreementPair_value]
def bestCuts (T S : BinaryProvider.Tree) : List (Option RMAF.Vertex)→Charged (Option (Option RMAF.Vertex))
 | []=>⟨none,1⟩
 | c::cs=>let a:=cutValid T S c;let r:=bestCuts T S cs
  ⟨if a.value then match r.value with
    | none=>some c | some d=>if cutLe c d then some c else some d
   else r.value,a.work+r.work+8⟩
@[simp] theorem bestCuts_value (T S : BinaryProvider.Tree) (cs : List (Option RMAF.Vertex)) :
 (bestCuts T S cs).value=RMAF.best Universal233.DepthOne.cutCost
  (fun c=>RMAF.agreement (treeValue T) (treeValue S) (Universal233.DepthOne.forest (treeValue S) c)) cs := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>
  simp only [bestCuts,cutValid_value,ih,RMAF.best]
  split
  · cases h : RMAF.best Universal233.DepthOne.cutCost
     (fun c=>RMAF.agreement (treeValue T) (treeValue S) (Universal233.DepthOne.forest (treeValue S) c)) cs
    · rfl
    · simp only [cutLe_value,decide_eq_true_eq]
  · rfl

def pretestBits (T S : BinaryProvider.Tree) : Charged Universal233.DepthOne.Result :=
 let p:=properPair T S
 if p.value then
  let c:=candidatesBits S;let b:=bestCuts T S c.value
  ⟨match b.value with | none=>.rejected | some c=>.found c,p.work+c.work+b.work+8⟩
 else ⟨.refused,p.work+4⟩
@[simp] theorem pretestBits_value (T S : BinaryProvider.Tree) :
 (pretestBits T S).value=Universal233.DepthOne.pretest01 (treeValue T) (treeValue S) := by
 simp only [pretestBits,Universal233.DepthOne.pretest01,properPair_value]
 split
 · simp only [candidatesBits_value,bestCuts_value]
   cases RMAF.best Universal233.DepthOne.cutCost
    (fun c=>RMAF.agreement (treeValue T) (treeValue S) (Universal233.DepthOne.forest (treeValue S) c))
    (Universal233.DepthOne.candidates (treeValue S)) <;> rfl
 · rfl
end GenericForest.BinaryProducer
