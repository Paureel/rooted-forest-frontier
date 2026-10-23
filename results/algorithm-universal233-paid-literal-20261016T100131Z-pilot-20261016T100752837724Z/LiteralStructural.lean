import LiteralAtoms
namespace Universal233.PaidLiteralDecisionWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork
open Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard Case322Extraction

/-- Compare a looked-up subtree to the constructed literal tree. -/
def atTreeMeter (T : Tree) (q : RMAF.Vertex) (U : Tree) : Measured Bool :=
 let s:=subtreeMeter T q
 match s.value with
 | none=>⟨false,s.work+2⟩
 | some V=>let e:=treeEqMeter U V;⟨e.value,s.work+e.work+2⟩

theorem at_tree_value (T : Tree) (q : RMAF.Vertex) (U : Tree) :
 (atTreeMeter T q U).value=decide (subtree T q=some U) := by
 apply Bool.eq_iff_iff.2
 simp only [atTreeMeter,subtree_value,decide_eq_true_eq]
 split <;> simp_all [tree_eq_value,eq_comm]

theorem at_tree_work (T : Tree) (q : RMAF.Vertex) (U : Tree) :
 (atTreeMeter T q U).work≤2*q.length+3*treeNodes U+3 := by
 have s:=subtree_work T q
 simp only [atTreeMeter]
 split
 · dsimp only;omega
 · rename_i V h;have e:=tree_eq_work U V;dsimp only;omega

/-- The bounded cherry existential pays each attempted address and endpoint order. -/
def cherryAtEitherMeter (T : Tree) (a b : Nat) (q : RMAF.Vertex) : Measured Bool :=
 let x:=atTreeMeter T q (.node (.leaf a) (.leaf b))
 if x.value then ⟨true,x.work+1⟩
 else let y:=atTreeMeter T q (.node (.leaf b) (.leaf a));⟨y.value,x.work+y.work+1⟩

theorem cherry_at_either_value (T : Tree) (a b : Nat) (q : RMAF.Vertex) :
 (cherryAtEitherMeter T a b q).value=decide (CherryAt T q a b ∨ CherryAt T q b a) := by
 simp only [cherryAtEitherMeter,at_tree_value]
 split <;> simp_all [CherryAt]

theorem cherry_at_either_work (T : Tree) (a b : Nat) (q : RMAF.Vertex) :
 (cherryAtEitherMeter T a b q).work≤4*q.length+25 := by
 have a1:=at_tree_work T q (.node (.leaf a) (.leaf b))
 have a2:=at_tree_work T q (.node (.leaf b) (.leaf a))
 simp only [treeNodes] at a1 a2
 simp only [cherryAtEitherMeter];split <;> dsimp only <;> omega

def cherryExistsMeter (T : Tree) (a b : Nat) : Measured Bool :=
 let v:=verticesMeter T;let z:=anyMeter (cherryAtEitherMeter T a b) v.value
 ⟨z.value,v.work+z.work+1⟩

theorem cherry_exists_value (T : Tree) (a b : Nat) :
 (cherryExistsMeter T a b).value=decide (∃q∈vertices T,CherryAt T q a b ∨ CherryAt T q b a) := by
 apply Bool.eq_iff_iff.2
 simp [cherryExistsMeter,any_value,cherry_at_either_value,vertices_value,List.any_eq_true]

def cherryBudget (n : Nat) :=64*n*n+(4*n+26)*(2*n)+2

theorem cherry_exists_work (T : Tree) (a b : Nat) :
 (cherryExistsMeter T a b).work≤cherryBudget (leaves T).length := by
 have v:=vertices_work T;have vc:=vertices_count T
 have z:=any_work (cherryAtEitherMeter T a b) (verticesMeter T).value (4*(leaves T).length+25) (by
  intro q hq;have w:=cherry_at_either_work T a b q;have d:=vertices_address T hq;omega)
 have sc:=Nat.mul_le_mul_left (4*(leaves T).length+26) (show (verticesMeter T).value.length≤2*(leaves T).length by rw [vertices_value];omega)
 simp only [cherryExistsMeter,cherryBudget];omega

/-- Re-extract both captured leaf lists for each bounded universal decision. -/
def labelPointMeter (C X : Tree) (c z : Nat) : Measured Bool :=
 let lc:=leavesMeter C;let lx:=leavesMeter X
 let mc:=containsMeter z lc.value;let mx:=containsMeter z lx.value
 ⟨decide (mc.value=(!mx.value && decide (z≠c))),lc.work+lx.work+mc.work+mx.work+4⟩

theorem label_point_value (C X : Tree) (c z : Nat) :
 (labelPointMeter C X c z).value=decide (z∈leaves C ↔ z∉leaves X ∧ z≠c) := by
 apply Bool.eq_iff_iff.2
 simp only [labelPointMeter,contains_value,leaves_value,decide_eq_true_eq]
 cases hc:(leaves C).contains z <;> cases hx:(leaves X).contains z <;> simp_all [List.contains_iff_mem]

def labelPointBudget (nc nx : Nat) :=4*nc*nc+4*nx*nx+2*nc+2*nx+6

theorem label_point_work (C X : Tree) (c z : Nat) :
 (labelPointMeter C X c z).work≤labelPointBudget (leaves C).length (leaves X).length := by
 have lc:=leaves_work C;have lx:=leaves_work X
 have mc:=contains_work z (leaves C);have mx:=contains_work z (leaves X)
 simp only [labelPointMeter,leaves_value,labelPointBudget];omega

def labelsMeter (T C X : Tree) (c : Nat) : Measured Bool :=
 let l:=leavesMeter T;let z:=allMeter (labelPointMeter C X c) l.value
 ⟨z.value,l.work+z.work+1⟩

theorem labels_value (T C X : Tree) (c : Nat) :
 (labelsMeter T C X c).value=decide (∀z∈leaves T,z∈leaves C ↔ z∉leaves X ∧ z≠c) := by
 apply Bool.eq_iff_iff.2
 simp [labelsMeter,all_value,leaves_value,label_point_value,List.all_eq_true]

def labelsBudget (nt nc nx : Nat) :=4*nt*nt+(labelPointBudget nc nx+1)*nt+2

theorem labels_work (T C X : Tree) (c : Nat) :
 (labelsMeter T C X c).work≤labelsBudget (leaves T).length (leaves C).length (leaves X).length := by
 have l:=leaves_work T
 have z:=all_work (labelPointMeter C X c) (leavesMeter T).value
  (labelPointBudget (leaves C).length (leaves X).length) (by intro z _;exact label_point_work C X c z)
 simp only [leaves_value] at z
 simp only [labelsMeter,labelsBudget];omega

/-- Each equality occurrence recomputes incident and the captured leaf list. -/
def incidentEqMeter (T X : Tree) (u v : RMAF.Vertex) : Measured Bool :=
 let x:=leavesMeter X;let i:=incidentMeter T x.value
 let e:=addressListsEqMeter [v,u] i.value
 ⟨e.value,x.work+i.work+e.work+3⟩

theorem incident_eq_value (T X : Tree) (u v : RMAF.Vertex) :
 (incidentEqMeter T X u v).value=decide (Rule5Local.incident T (leaves X)=[v,u]) := by
 rw [incidentEqMeter,address_lists_eq_value,incident_value,leaves_value]
 simp [eq_comm]

def minimalMemMeter (T X : Tree) (q : RMAF.Vertex) : Measured Bool :=
 let x:=leavesMeter X;let m:=minimalMeter x.value T;let c:=containsAddressMeter q m.value
 ⟨c.value,x.work+m.work+c.work+2⟩

theorem minimal_mem_value (T X : Tree) (q : RMAF.Vertex) :
 (minimalMemMeter T X q).value=decide (q∈minimalVertices (leaves X) T) := by
 apply Bool.eq_iff_iff.2
 simp [minimalMemMeter,contains_address_value,minimal_value,leaves_value,List.contains_iff_mem]

def tailMemMeter (T X : Tree) (q : RMAF.Vertex) : Measured Bool :=
 let d:=dropLastMeter q;let m:=minimalMemMeter T X d.value
 ⟨m.value,d.work+m.work+1⟩

theorem tail_mem_value (T X : Tree) (q : RMAF.Vertex) :
 (tailMemMeter T X q).value=decide (q.dropLast∈minimalVertices (leaves X) T) := by
 simp only [tailMemMeter,minimal_mem_value,drop_last_value]

def boundaryEqMeter (S X : Tree) (p : RMAF.Vertex) : Measured Bool :=
 let s:=subtreeLabelsMeter S p;let x:=leavesMeter X;let e:=natListEqMeter s.value x.value
 ⟨e.value,s.work+x.work+e.work+2⟩

theorem boundary_eq_value (S X : Tree) (p : RMAF.Vertex) :
 (boundaryEqMeter S X p).value=decide (subtreeLabels S p=leaves X) := by
 simp only [boundaryEqMeter,nat_list_eq_value,subtree_labels_value,leaves_value]

end Universal233.PaidLiteralDecisionWork
