import CheckFamilies
namespace GenericForest.CheckCorrespondence
open RMAF ForestState RestrictionBridge Universal233 WholeSourceWork CoreWork

def meterLabels : Option Tree → Charged (List Nat)
 | none=>⟨[],1⟩ | some t=>meterLeaves t
@[simp] theorem meterLabels_value (T) : (meterLabels T).value=labels T := by cases T <;> simp [meterLabels,labels]

def meterProper (T : Option Tree) (ss : List Tree) : Charged Bool :=
 let a:=meterLabels T;let b:=meterNodup a.value;let c:=meterSourceLeaves ss
 let d:=meterPartition a.value c.value
 ⟨b.value&&d.value,a.work+b.work+c.work+d.work+4⟩
@[simp] theorem meterProper_value (T ss) : (meterProper T ss).value=proper T ss := by simp [meterProper,proper]

def meterTargetAgrees : Option Tree → Tree → List Nat → Charged Bool
 | none,_,_=>⟨false,1⟩ | some t,s,B=>meterRestrictionAgrees t s B
@[simp] theorem meterTargetAgrees_value (T s B) : (meterTargetAgrees T s B).value=targetAgrees T s B := by
 cases T <;> simp [meterTargetAgrees,targetAgrees]

def meterTargetEmbeddings : Option Tree → Forest → Charged Bool
 | none,F=>⟨F.isEmpty,1⟩ | some t,F=>meterPairwise t F
@[simp] theorem meterTargetEmbeddings_value (T F) :
 (meterTargetEmbeddings T F).value=targetEmbeddings T F := by cases T <;> simp [meterTargetEmbeddings,targetEmbeddings]

def meterSourceCheck (T : Option Tree) (F : Forest) (s : Tree) : Charged Bool :=
 let a:=meterLeaves s;let G:=meterFamily a.value F
 let b:=meterLeaves s;let p:=meterPartition b.value G.value
 let r:=meterAll (meterTargetAgrees T s) G.value
 let e:=meterPairwise s G.value
 ⟨p.value&&r.value&&e.value,a.work+G.work+b.work+p.work+r.work+e.work+8⟩
@[simp] theorem meterSourceCheck_value (T F s) : (meterSourceCheck T F s).value=sourceCheck T F s := by
 simp [meterSourceCheck,sourceCheck]

def meterSourceContainment (B : List Nat) (ss : List Tree) : Charged Bool :=
 meterAny (fun s=>let a:=meterLeaves s;let c:=meterContained B a.value;⟨c.value,a.work+c.work+2⟩) ss
@[simp] theorem meterSourceContainment_value (B ss) :
 (meterSourceContainment B ss).value=ss.any (fun s=>contained B (leaves s)) := by simp [meterSourceContainment]

def meterAgrees (T : Option Tree) (ss : List Tree) (F : Forest) : Charged Bool :=
 let p:=meterProper T ss;let a:=meterLabels T;let f:=meterPartition a.value F
 let c:=meterAll (fun B=>meterSourceContainment B ss) F
 let e:=meterTargetEmbeddings T F;let s:=meterAll (meterSourceCheck T F) ss
 ⟨p.value&&f.value&&c.value&&e.value&&s.value,p.work+a.work+f.work+c.work+e.work+s.work+8⟩
@[simp] theorem meterAgrees_value (T ss F) : (meterAgrees T ss F).value=agrees T ss F := by
 simp [meterAgrees,agrees]

/-- Length traversals, subtraction and comparison are billed even on rejection.
The scalar slots are unit costs here; a bit implementation needs a scalar cap. -/
def meterAccepted (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Charged Bool :=
 let a:=meterAgrees T ss F
 ⟨a.value&&decide (additionalCost ss F≤q),a.work+6*(F.length+ss.length+1)+4⟩
@[simp] theorem meterAccepted_value (T ss q F) : (meterAccepted T ss q F).value=accepted T ss q F := by
 simp [meterAccepted,accepted]

def meterChecked (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Charged (Option Forest) :=
 let a:=meterAccepted T ss q F
 ⟨if a.value then some F else none,a.work+2⟩
@[simp] theorem meterChecked_value (T ss q F) : (meterChecked T ss q F).value=checked T ss q F := by
 simp [meterChecked,checked]
end GenericForest.CheckCorrespondence
