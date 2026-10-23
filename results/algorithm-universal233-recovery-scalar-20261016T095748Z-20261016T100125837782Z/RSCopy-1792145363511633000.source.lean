import RSOutputs
namespace OrdinaryDispatch.RecoveryBits
open Universal233 WholeSourceWork CoreProgram

structure BitGroup where
 origin : List Bool
 labels : List (List Bool)
 color : List Bool
 deriving DecidableEq,Repr
inductive BitTree where
 | leaf : BitGroup→BitTree
 | node : List Bool→BitTree→BitTree→BitTree
 deriving DecidableEq,Repr
structure BitOutput where
 partition : List (List (List Bool))
 sourceCuts : List (List Bool)
 deriving DecidableEq,Repr

/-- These projections occur in specifications, never in represented producers. -/
def viewGroup (g : BitGroup) : Group := ⟨g.origin,g.labels.map decode,decode g.color⟩
def viewTree : BitTree→GTree
 | .leaf g=>.leaf (viewGroup g)
 | .node p l r=>.node p (viewTree l) (viewTree r)
def viewOutput (o : BitOutput) : Output := ⟨o.partition.map (List.map decode),o.sourceCuts⟩

def arrayCells : List (List Bool)→Nat
 | []=>0
 | b::bs=>b.length+1+arrayCells bs

def copyArrays : List (List Bool)→Charged (List (List Bool))
 | []=>⟨[],2⟩
 | b::bs=>let c:=copyBits b;let r:=copyArrays bs;⟨c.value::r.value,c.work+r.work+4⟩
@[simp] theorem copyArrays_value (xs : List (List Bool)) : (copyArrays xs).value=xs := by
 induction xs <;> simp_all [copyArrays]
theorem copyArrays_work (xs : List (List Bool)) : (copyArrays xs).work≤8*(arrayCells xs+1) := by
 induction xs with
 | nil=>simp [copyArrays,arrayCells]
 | cons b bs ih=>simp only [copyArrays,copyBits_work,arrayCells,Nat.mul_add,Nat.mul_one] at *;omega

def groupCells (g : BitGroup) : Nat := g.origin.length+arrayCells g.labels+g.color.length+1

def copyGroup (g : BitGroup) : Charged BitGroup :=
 let a:=copyBits g.origin;let l:=copyArrays g.labels;let c:=copyBits g.color
 ⟨⟨a.value,l.value,c.value⟩,a.work+l.work+c.work+12⟩
@[simp] theorem copyGroup_value (g : BitGroup) : (copyGroup g).value=g := by
 simp [copyGroup]
theorem copyGroup_work (g : BitGroup) : (copyGroup g).work≤32*groupCells g := by
 have a:=copyArrays_work g.labels
 simp only [copyGroup,copyBits_work,groupCells,Nat.mul_add,Nat.mul_one] at *;omega

def treeCells : BitTree→Nat
 | .leaf g=>1+groupCells g
 | .node p l r=>1+p.length+treeCells l+treeCells r

def copyTree : BitTree→Charged BitTree
 | .leaf g=>let r:=copyGroup g;⟨.leaf r.value,r.work+4⟩
 | .node p l r=>let a:=copyBits p;let x:=copyTree l;let y:=copyTree r
   ⟨.node a.value x.value y.value,a.work+x.work+y.work+12⟩
@[simp] theorem copyTree_value (t : BitTree) : (copyTree t).value=t := by
 induction t <;> simp_all [copyTree]
theorem copyTree_work (t : BitTree) : (copyTree t).work≤64*treeCells t := by
 induction t with
 | leaf g=>have a:=copyGroup_work g;simp only [copyTree,treeCells,Nat.mul_add,Nat.mul_one];omega
 | node p l r il ir=>simp only [copyTree,copyBits_work,treeCells,Nat.mul_add,Nat.mul_one];omega

def forestCells : List (List (List Bool))→Nat
 | []=>0
 | b::bs=>arrayCells b+1+forestCells bs

def copyForest : List (List (List Bool))→Charged (List (List (List Bool)))
 | []=>⟨[],2⟩
 | b::bs=>let c:=copyArrays b;let r:=copyForest bs;⟨c.value::r.value,c.work+r.work+4⟩
@[simp] theorem copyForest_value (xs : List (List (List Bool))) : (copyForest xs).value=xs := by
 induction xs <;> simp_all [copyForest]
theorem copyForest_work (xs : List (List (List Bool))) : (copyForest xs).work≤16*(forestCells xs+1) := by
 induction xs with
 | nil=>simp [copyForest,forestCells]
 | cons b bs ih=>have c:=copyArrays_work b;simp only [copyForest,forestCells,Nat.mul_add,Nat.mul_one] at *;omega

def outputCells (o : BitOutput) : Nat := forestCells o.partition+arrayCells o.sourceCuts+1

def copyOutput (o : BitOutput) : Charged BitOutput :=
 let p:=copyForest o.partition;let c:=copyArrays o.sourceCuts
 ⟨⟨p.value,c.value⟩,p.work+c.work+8⟩
@[simp] theorem copyOutput_value (o : BitOutput) : (copyOutput o).value=o := by simp [copyOutput]
theorem copyOutput_work (o : BitOutput) : (copyOutput o).work≤32*outputCells o := by
 have p:=copyForest_work o.partition;have c:=copyArrays_work o.sourceCuts
 simp only [copyOutput,outputCells,Nat.mul_add,Nat.mul_one] at *;omega

/-- A new fixed-width counter is produced from copied supplied operands. Overflow
is an explicit value premise, never erased by a certificate projection. -/
def counterAdd (W : Nat) (xs ys : List Bool) : Charged (List Bool) :=
 let a:=copyBits xs;let b:=copyBits ys
 let s:=addAtWidth W a.value b.value
 let c:=copyBits s.value
 ⟨c.value,a.work+b.work+s.work+c.work+8⟩
@[simp] theorem counterAdd_value (W : Nat) (xs ys : List Bool) (fits : decode xs+decode ys<2^W) :
 decode (counterAdd W xs ys).value=decode xs+decode ys := by
 simp [counterAdd,addAtWidth_value W xs ys fits]
theorem counterAdd_length (W : Nat) (xs ys : List Bool) : (counterAdd W xs ys).value.length≤W := by
 simp only [counterAdd,copyBits_value,addAtWidth,List.length_take];exact Nat.min_le_left _ _
theorem counterAdd_work (W : Nat) (xs ys : List Bool) (xl : xs.length≤W) (yl : ys.length≤W) :
 (counterAdd W xs ys).work≤64*(W+1) := by
 have a:=addAtWidth_work W xs ys xl yl
 have l:(addAtWidth W xs ys).value.length≤W:=by simp only [addAtWidth,List.length_take];exact Nat.min_le_left _ _
 simp only [counterAdd,copyBits_work,copyBits_value];omega

def counterInc (W : Nat) (xs : List Bool) : Charged (List Bool) := counterAdd W xs [true]
@[simp] theorem counterInc_value (W : Nat) (xs : List Bool) (fits : decode xs+1<2^W) :
 decode (counterInc W xs).value=decode xs+1 := by
 exact counterAdd_value W xs [true] (by simpa [decode,bit] using fits)
theorem counterInc_work (W : Nat) (xs : List Bool) (positive : 1≤W) (xl : xs.length≤W) :
 (counterInc W xs).work≤64*(W+1) := counterAdd_work W xs [true] xl (by simpa)
end OrdinaryDispatch.RecoveryBits
