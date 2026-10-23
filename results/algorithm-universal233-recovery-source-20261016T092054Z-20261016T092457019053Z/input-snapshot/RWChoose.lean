import RWTree
namespace OrdinaryDispatch.RecoveryLocalWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork

def meterUniqueTest (gs : List Group) (g : Group) : Charged Bool :=
 let f:=meterFilter (fun h:Group=>⟨h.color==g.color,4⟩) gs
 let n:=meterLength f.value
 ⟨n.value==1,f.work+n.work+4⟩
@[simp] theorem meterUniqueTest_value (gs : List Group) (g : Group) :
 (meterUniqueTest gs g).value=(((gs.filter (fun h=>h.color==g.color)).length)==1) := by simp [meterUniqueTest]
theorem meterUniqueTest_bound (gs : List Group) (g : Group) :
 (meterUniqueTest gs g).work≤16*(gs.length+1) := by
 have f:=meterFilter_bound (fun h:Group=>⟨h.color==g.color,4⟩) gs 4 (by intro _ _;exact Nat.le_refl _)
 have n:=meterLength_work (gs.filter (fun h=>h.color==g.color))
 have len:=List.length_filter_le (fun h:Group=>h.color==g.color) gs
 simp only [meterUniqueTest,meterFilter_value];omega

/-- Source groups/all/find/filter/mixed-cherry operations are expanded. Later
priority suffixes may be overcharged; no whole choose oracle is a unit slot. -/
def meterChoose (t : GTree) : Charged Choice :=
 let g:=meterGroups t;let m:=meterMixed t
 match g.value with
 | []=>⟨.refuse "empty current source",g.work+m.work+8⟩
 | first::_=>
  let a:=meterAll (fun h:Group=>⟨h.color==first.color,4⟩) g.value
  let f:=meterFind (meterUniqueTest g.value) g.value
  ⟨if a.value then .finish else match f.value with
    | some x=>.one x
    | none=>match m.value with
      | some (x,y)=>if x.color==y.color then .refuse "unnormalized homogeneous cherry" else .two x y
      | none=>.refuse "no mixed cherry in multicolor source",
    g.work+m.work+a.work+f.work+16⟩
@[simp] theorem meterChoose_value (t : GTree) : (meterChoose t).value=choose t := by
 simp only [meterChoose,meterGroups_value,meterMixed_value,meterAll_value,meterFind_value,meterUniqueTest_value,choose]
 cases h:groups t with
 | nil=>rfl
 | cons first gs=>simp only [h];rfl

theorem meterChoose_bound (t : GTree) (N : Nat) (size : footprint t≤N) :
 (meterChoose t).work≤128*(N+1)^3 := by
 have group:=meterGroups_bound t N size
 have gcap:=Nat.mul_le_mul_left (16*(N+1)) (Nat.le_trans size (Nat.le_succ N))
 have mix:=meterMixed_bound t
 have glen:=Nat.le_trans (groups_length t) size
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 have p1 : N+1≤(N+1)^3:=by simpa using pow_mono N 1 3 (by decide)
 have p2:=pow_mono N 2 3 (by decide)
 have gg : (meterGroups t).work≤16*(N+1)^3:=Nat.le_trans group
  (Nat.le_trans gcap (by simpa only [Nat.pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left 16 p2))
 simp only [meterChoose,meterGroups_value,meterMixed_value]
 cases h:groups t with
 | nil=>simp only [h];omega
 | cons first gs=>
  have all:=meterAll_bound (fun h:Group=>⟨h.color==first.color,4⟩) (groups t) 4 (by intro _ _;exact Nat.le_refl _)
  have ff:=meterFind_bound (meterUniqueTest (groups t)) (groups t) (16*(N+1))
   (fun g _=>Nat.le_trans (meterUniqueTest_bound (groups t) g) (Nat.mul_le_mul_left 16 (Nat.add_le_add_right glen 1)))
  have scale:=Nat.mul_le_mul (show 16*(N+1)+4≤20*(N+1) by omega) (Nat.add_le_add_right glen 1)
  have fcap : (meterFind (meterUniqueTest (groups t)) (groups t)).work≤20*(N+1)^3:=Nat.le_trans ff
   (Nat.le_trans (by simpa only [Nat.pow_two,Nat.mul_assoc] using scale) (Nat.mul_le_mul_left 20 p2))
  simp only [h,List.length_cons] at all fcap glen
  simp only [h];omega

/-- Chosen origins are bounded by the actual current tree footprint. No
successful erase, accepted recovery or separate payload cap is assumed. -/
theorem choose_one_origin (t : GTree) (g : Group) (h : choose t=.one g) :
 g.origin.length≤footprint t := by
 have mem:=(Integration.choose_one_selected t g h).1
 have size:=group_size t g mem;omega

theorem choose_two_origins (t : GTree) (a b : Group) (h : choose t=.two a b) :
 a.origin.length≤footprint t ∧ b.origin.length≤footprint t := by
 obtain ⟨p,cherry,ne⟩:=Integration.choose_two_selected t a b h
 have ma:=Integration.groupLeaf_mem_groups t (p++[false]) a (Integration.gcherry_left cherry)
 have mb:=Integration.groupLeaf_mem_groups t (p++[true]) b (Integration.gcherry_right cherry)
 have sa:=group_size t a ma;have sb:=group_size t b mb
 constructor <;> omega
end OrdinaryDispatch.RecoveryLocalWork
