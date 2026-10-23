import PersistentProper
namespace GenericForest.BinaryProvider
open Universal233.WholeSourceWork GenericForest.ScalarBits GenericForest.CheckCorrespondence
def sourceCheckLabels (C : Capacity) (T : Option Tree) (F : Forest) (s : Tree) : Charged Bool:=
 let a:=leavesCopy s;let G:=familyLabels a.value F
 let b:=leavesCopy s;let p:=partitionLabels C b.value G.value
 let r:=allChecks (targetAgreesLabels T s) G.value;let e:=pairwiseLabels s G.value
 ⟨p.value&&r.value&&e.value,a.work+G.work+b.work+p.work+r.work+e.work+8⟩
theorem sourceCheckLabels_projects (W : Nat) (C : Capacity) (T : Option Tree) (F : Forest) (s : Tree)
 (cw : C.length≤W) (cp : 0<C.length) (tc : TargetWidth W T) (sc : TreeWidth W s)
 (fc : ForestWidth W F) (fits : F.flatten.length<2^C.length) :
 Projects W id (sourceCheckLabels C T F s) (meterSourceCheck (targetValue T) (forestValue F) (treeValue s)) := by
 have a:=leavesCopy_projects s W sc
 have sw : BlockWidth W (leavesCopy s).value:=by simpa only [leavesCopy_value,TreeWidth] using sc
 have G:=familyLabels_projects W (leavesCopy s).value F sw fc
 have gw:=familyLabels_width W (leavesCopy s).value F fc
 have gl:=familyLabels_cells (leavesCopy s).value F
 have p:=partitionLabels_projects W C (leavesCopy s).value (familyLabels (leavesCopy s).value F).value
  cw cp sw gw (Nat.lt_of_le_of_lt gl fits)
 have r:=allChecks_projects W blockValue (targetAgreesLabels T s)
  (meterTargetAgrees (targetValue T) (treeValue s)) (familyLabels (leavesCopy s).value F).value
  (fun B hb=>targetAgreesLabels_projects W T s B tc sc (gw B hb))
 have e:=pairwiseLabels_projects W s (familyLabels (leavesCopy s).value F).value sc gw
 have k:=beta_positive W
 simp only [Projects,id_eq,forestValue] at a G p r e ⊢
 simp only [sourceCheckLabels,meterSourceCheck,←a.1,←G.1]
 constructor
 · simp only [p.1,r.1,e.1]
 · simp only [Nat.mul_add];omega

def agreesLabels (C : Capacity) (T : Option Tree) (ss : List Tree) (F : Forest) : Charged Bool:=
 let p:=properLabels C T ss;let a:=targetLabelsCopy T;let f:=partitionLabels C a.value F
 let c:=allChecks (fun B=>sourceContainmentLabels B ss) F
 let e:=targetEmbeddingsLabels T F;let s:=allChecks (sourceCheckLabels C T F) ss
 ⟨p.value&&f.value&&c.value&&e.value&&s.value,p.work+a.work+f.work+c.work+e.work+s.work+8⟩
theorem agreesLabels_projects (W : Nat) (C : Capacity) (T : Option Tree) (ss : List Tree) (F : Forest)
 (cw : C.length≤W) (cp : 0<C.length) (tc : TargetWidth W T) (sc : SourcesWidth W ss)
 (fc : ForestWidth W F) (fitF : F.flatten.length<2^C.length)
 (fitS : (sourceLeavesCopy ss).value.flatten.length<2^C.length) :
 Projects W id (agreesLabels C T ss F) (meterAgrees (targetValue T) (sourcesValue ss) (forestValue F)) := by
 have p:=properLabels_projects W C T ss cw cp tc sc fitS
 have a:=targetLabelsCopy_projects W T tc
 have f:=partitionLabels_projects W C (targetLabelsCopy T).value F cw cp (targetLabelsCopy_width W T tc) fc fitF
 have c:=allChecks_projects W blockValue (fun B=>sourceContainmentLabels B ss)
  (fun B=>meterSourceContainment B (sourcesValue ss)) F
  (fun B hb=>sourceContainmentLabels_projects W B ss (fc B hb) sc)
 have e:=targetEmbeddingsLabels_projects W T F tc fc
 have s:=allChecks_projects W treeValue (sourceCheckLabels C T F)
  (meterSourceCheck (targetValue T) (forestValue F)) ss
  (fun t ht=>sourceCheckLabels_projects W C T F t cw cp tc (sc t ht) fc fitF)
 have k:=beta_positive W
 simp only [Projects,id_eq,forestValue,sourcesValue] at p a f c e s ⊢
 simp only [agreesLabels,meterAgrees,←a.1]
 constructor
 · simp only [p.1,f.1,c.1,e.1,s.1]
 · simp only [Nat.mul_add];omega
end GenericForest.BinaryProvider
