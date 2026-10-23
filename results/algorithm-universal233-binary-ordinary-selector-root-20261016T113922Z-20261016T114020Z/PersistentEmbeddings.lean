import PersistentHull
namespace GenericForest.BinaryProvider
open Universal233.WholeSourceWork GenericForest.ScalarBits GenericForest.CheckCorrespondence

/-- Address comparisons are the frozen direct List Bool evaluator. They read
persistent original addresses without numerical encoding or decoding. -/
def hullPairLabels (T : Tree) (B C : Block) : Charged Bool:=
 let a:=minimalLabels B T;let b:=minimalLabels C T;let d:=meterDisjoint a.value b.value
 ⟨d.value,a.work+b.work+d.work+2⟩
theorem hullPairLabels_projects (W : Nat) (T : Tree) (B C : Block)
 (tc : TreeWidth W T) (bc : BlockWidth W B) (cc : BlockWidth W C) :
 Projects W id (hullPairLabels T B C) (meterHullPair (treeValue T) (blockValue B) (blockValue C)) := by
 have a:=minimalLabels_projects W B T bc tc;have b:=minimalLabels_projects W C T cc tc
 have p:=beta_positive W
 have d:=Nat.mul_le_mul_right (meterDisjoint (minimalLabels B T).value (minimalLabels C T).value).work p
 simp only [Projects,id_eq] at a b ⊢
 simp only [hullPairLabels,meterHullPair,←a.1,←b.1]
 constructor
 · trivial
 · simp only [Nat.mul_add];omega

def pairwiseLabels (T : Tree) : Forest→Charged Bool
 | []=>⟨true,1⟩
 | B::F=>let a:=allChecks (hullPairLabels T B) F;let r:=pairwiseLabels T F
          ⟨a.value&&r.value,a.work+r.work+4⟩
theorem pairwiseLabels_projects (W : Nat) (T : Tree) (F : Forest) (tc : TreeWidth W T) (fc : ForestWidth W F) :
 Projects W id (pairwiseLabels T F) (meterPairwise (treeValue T) (forestValue F)) := by
 have p:=beta_positive W
 induction F with
 | nil=>simp [Projects,pairwiseLabels,meterPairwise,forestValue];exact p
 | cons B F ih=>
  have a:=allChecks_projects W blockValue (hullPairLabels T B) (meterHullPair (treeValue T) (blockValue B)) F
   (fun C hc=>hullPairLabels_projects W T B C tc (fc B (by simp)) (fc C (by simp [hc])))
  have r:=ih (fun C hc=>fc C (by simp [hc]))
  simp only [Projects,id_eq,forestValue] at a r ⊢
  simp only [pairwiseLabels,meterPairwise,List.map_cons]
  constructor
  · simp only [a.1,r.1]
  · simp only [Nat.mul_add];omega

theorem familyLabels_mem (U : Block) (F : Forest) (B : Block) (h : B∈(familyLabels U F).value) : B∈F := by
 induction F with
 | nil=>simp [familyLabels] at h
 | cons A F ih=>
  simp only [familyLabels] at h
  split at h
  · rcases List.mem_cons.mp h with rfl|hb
    · simp
    · exact List.mem_cons_of_mem A (ih hb)
  · exact List.mem_cons_of_mem A (ih h)
theorem familyLabels_width (W : Nat) (U : Block) (F : Forest) (fc : ForestWidth W F) :
 ForestWidth W (familyLabels U F).value:=fun B hb=>fc B (familyLabels_mem U F B hb)
theorem familyLabels_cells (U : Block) (F : Forest) : (familyLabels U F).value.flatten.length≤F.flatten.length := by
 induction F with
 | nil=>simp [familyLabels]
 | cons B F ih=>
  simp only [familyLabels]
  split <;> simp only [List.flatten_cons,List.length_append] <;> omega
end GenericForest.BinaryProvider
