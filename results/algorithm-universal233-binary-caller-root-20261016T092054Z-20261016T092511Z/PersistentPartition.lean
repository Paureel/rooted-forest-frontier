import PersistentCount
namespace GenericForest.BinaryProvider
open Universal233.WholeSourceWork GenericForest.ScalarBits GenericForest.CheckCorrespondence

/-- Every count closure repeats and pays for the actual label materialization. -/
def partitionLabels (C : Capacity) (L : Block) (F : Forest) : Charged Bool :=
 let nonempty:=allChecks (fun B : Block=>⟨!B.isEmpty,1⟩) F
 let counts:=allChecks (fun x=>let cells:=flattenLabels F;let count:=countLabel C x cells.value
                             let eq:=copiedEqual count.value [true]
                             ⟨eq.value,cells.work+count.work+eq.work+4⟩) L
 let cells:=flattenLabels F
 let labels:=allChecks (fun x=>containsLabel x L) cells.value
 ⟨nonempty.value&&counts.value&&labels.value,nonempty.work+counts.work+cells.work+labels.work+4⟩

theorem partitionLabels_projects (W : Nat) (C : Capacity) (L : Block) (F : Forest)
 (cw : C.length≤W) (cp : 0<C.length) (lc : BlockWidth W L) (fc : ForestWidth W F)
 (fits : F.flatten.length<2^C.length) :
 Projects W id (partitionLabels C L F) (meterPartition (blockValue L) (forestValue F)) := by
 have bw : BlockWidth W F.flatten:=by
  intro x hx
  obtain ⟨B,hB,hx⟩:=List.mem_flatten.mp hx
  exact fc B hB x hx
 have p:=beta_positive W
 have a:=allChecks_projects W blockValue (fun B : Block=>⟨!B.isEmpty,1⟩)
  (fun B : List Nat=>⟨!B.isEmpty,1⟩) F (by
   intro B hB
   simp only [Projects,id_eq]
   constructor
   · cases B <;> rfl
   · simpa using p)
 have cells:=flattenLabels_projects F W fc
 have b:=allChecks_projects W labelValue
  (fun x=>let f:=flattenLabels F;let c:=countLabel C x f.value;let e:=copiedEqual c.value [true];⟨e.value,f.work+c.work+e.work+4⟩)
  (fun x=>let f:=meterFlatten (forestValue F);let c:=meterCount x f.value;⟨c.value==1,f.work+c.work+4⟩) L (by
   intro x hx
   have c:=countLabel_projects W C x F.flatten cw (lc x hx) bw fits
   have e:=copiedEqual_work W (countLabel C x F.flatten).value [true]
    (Nat.le_trans (countLabel_length C x F.flatten) cw) (by simp;omega)
   have ev:=copiedEqual_value (countLabel C x F.flatten).value [true]
   simp only [Projects,id_eq] at c cells ⊢
   simp only [flattenLabels_value,meterFlatten_value,forestValue_flatten] at cells ⊢
   constructor
   · simpa only [ev,decode,bit,ite_true,Nat.mul_zero,Nat.add_zero,c.1] using (rfl : ((meterCount (labelValue x) (blockValue F.flatten)).value==1)=_)
   · simp only [Nat.mul_add] at cells ⊢
     unfold ScalarBits.beta at c cells ⊢;omega)
 have d:=allChecks_projects W labelValue (fun x=>containsLabel x L)
  (fun x=>meterContains x (blockValue L)) F.flatten (fun x hx=>containsLabel_projects W x L (bw x hx) lc)
 simp only [Projects,id_eq] at a b cells d ⊢
 simp only [partitionLabels,meterPartition,flattenLabels_value,meterFlatten_value,forestValue_flatten]
 simp only [flattenLabels_value,meterFlatten_value,forestValue_flatten,forestValue,blockValue] at a b cells d ⊢
 have flat : (List.map blockValue F).flatten=List.map labelValue F.flatten:=by simpa only [forestValue,blockValue] using forestValue_flatten F
 simp only [flat] at b ⊢
 constructor
 · simp only [a.1,b.1,d.1]
 · simp only [Nat.mul_add];omega
end GenericForest.BinaryProvider
