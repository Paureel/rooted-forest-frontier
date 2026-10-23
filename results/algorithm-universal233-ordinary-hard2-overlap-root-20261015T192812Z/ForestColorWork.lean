import Work
import WholeMass

/-! Problem-specific source-operation meter for the literal original-label
color callbacks. No unit-cost color oracle or assumed work/simulation field. -/
namespace Universal233.WholeSourceWork
open RMAF VertexGeometry CoreProgram CoreWork WholeSourceMass

structure Charged (α : Type) where
  value : α
  work : Nat
  deriving Repr

def meterContains (x : Nat) : List Nat → Charged Bool
  | [] => ⟨false,1⟩
  | y::ys => if x == y then ⟨true,4⟩ else
      let r := meterContains x ys
      ⟨r.value,4+r.work⟩

@[simp] theorem meterContains_value (x : Nat) (D : List Nat) :
    (meterContains x D).value = D.contains x := by
  induction D with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x = y <;> simp [meterContains,List.contains_cons,ih,h]

theorem meterContains_bound (x : Nat) (D : List Nat) :
    (meterContains x D).work ≤ 4*(D.length+1) := by
  induction D with
  | nil => simp [meterContains]
  | cons y ys ih =>
    simp only [meterContains,List.length_cons]
    split <;> simp only [Charged.work] <;> omega

def meterLeafList (D : List Nat) : Tree → Charged (List RMAF.Vertex)
  | .leaf x =>
    let m := meterContains x D
    ⟨if m.value then [[]] else [],m.work+8⟩
  | .node l r =>
    let a := meterLeafList D l
    let b := meterLeafList D r
    ⟨prependSide false a.value ++ prependSide true b.value,
      a.work+b.work+8*(a.value.length+b.value.length+1)⟩

@[simp] theorem meterLeafList_value (D : List Nat) (T : Tree) :
    (meterLeafList D T).value = leafList D T := by
  induction T with
  | leaf x => simp [meterLeafList,leafList]
  | node l r ihl ihr => simp [meterLeafList,leafList,ihl,ihr]

theorem leafList_length (D : List Nat) (T : Tree) :
    (leafList D T).length ≤ treeNodes T := by
  induction T with
  | leaf x => simp only [leafList,treeNodes]; split <;> simp
  | node l r ihl ihr =>
    simp only [leafList,prependSide,List.length_append,List.length_map,treeNodes]
    omega

/-- A uniform per-target-constructor source bound, with the target size M
supplied as a numerical upper bound; no runtime claim is an input. -/
theorem meterLeafList_bound (D : List Nat) (T : Tree) (M : Nat)
    (hM : treeNodes T ≤ M) :
    (meterLeafList D T).work ≤ 16*(D.length+M+2)*treeNodes T := by
  induction T with
  | leaf x =>
    have hm := meterContains_bound x D
    simp only [meterLeafList,treeNodes,Nat.mul_one]
    omega
  | node l r ihl ihr =>
    have hl : treeNodes l ≤ M := by simp only [treeNodes] at hM; omega
    have hr : treeNodes r ≤ M := by simp only [treeNodes] at hM; omega
    have hwl := ihl hl
    have hwr := ihr hr
    have hll := leafList_length D l
    have hlr := leafList_length D r
    let K := 16*(D.length+M+2)
    change (meterLeafList D l).work ≤ K*treeNodes l at hwl
    change (meterLeafList D r).work ≤ K*treeNodes r at hwr
    have hk : 8*((leafList D l).length+(leafList D r).length+1) ≤ K := by
      dsimp [K]
      simp only [treeNodes] at hM
      omega
    change (meterLeafList D l).work+(meterLeafList D r).work+
      8*((meterLeafList D l).value.length+(meterLeafList D r).value.length+1) ≤
      K*(1+treeNodes l+treeNodes r)
    rw [meterLeafList_value,meterLeafList_value]
    calc
      _ ≤ K*treeNodes l+K*treeNodes r+K := by omega
      _ = _ := by simp only [Nat.mul_add,Nat.mul_one]; omega

/-- Literal deletion-region recursion, charged per examined address bit. -/
def meterRegion : RMAF.Vertex → RMAF.Vertex → Charged Nat
  | [], [] => ⟨3,2⟩
  | [], false::_ => ⟨0,2⟩
  | [], true::_ => ⟨1,2⟩
  | _::_, [] => ⟨2,2⟩
  | s::v,t::a => if s=t then
      let r := meterRegion v a
      ⟨r.value,4+r.work⟩ else ⟨2,4⟩

@[simp] theorem meterRegion_value (v a : RMAF.Vertex) :
    (meterRegion v a).value = region v a := by
  induction v generalizing a with
  | nil => cases a with
    | nil => rfl
    | cons t a => cases t <;> rfl
  | cons s v ih => cases a with
    | nil => rfl
    | cons t a => by_cases h : s=t <;> simp [meterRegion,region,ih,h]

theorem meterRegion_bound (v a : RMAF.Vertex) :
    (meterRegion v a).work ≤ 4*(v.length+1) := by
  induction v generalizing a with
  | nil => cases a with
    | nil => decide
    | cons t a => cases t <;> simp [meterRegion]
  | cons s v ih => cases a with
    | nil => simp only [meterRegion,List.length_cons]; omega
    | cons t a =>
      have h := ih a
      simp only [meterRegion,List.length_cons]
      split <;> simp only [Charged.work] <;> omega

def meterColorLabel (T : Tree) (v : RMAF.Vertex) (x : Nat) : Charged Nat :=
  let a := meterLeafList [x] T
  let b := meterRegion v (a.value.headD [])
  ⟨b.value,a.work+b.work+3⟩

@[simp] theorem meterColorLabel_value (T : Tree) (v : RMAF.Vertex) (x : Nat) :
    (meterColorLabel T v x).value = colorLabel T v x := by
  simp [meterColorLabel,colorLabel]

def colorCap (T : Tree) (v : RMAF.Vertex) : Nat :=
  16*(treeNodes T+3)*treeNodes T+4*(v.length+1)+3

theorem meterColorLabel_bound (T : Tree) (v : RMAF.Vertex) (x : Nat) :
    (meterColorLabel T v x).work ≤ colorCap T v := by
  have ha := meterLeafList_bound [x] T (treeNodes T) (Nat.le_refl _)
  have hb := meterRegion_bound v ((meterLeafList [x] T).value.headD [])
  simp only [List.length_singleton] at ha
  have he : 1+treeNodes T+2 = treeNodes T+3 := by omega
  rw [he] at ha
  simp only [meterColorLabel,colorCap]
  omega

inductive Local where
  | keep
  | single (v : RMAF.Vertex)
  | joint (v w : RMAF.Vertex)
  deriving Repr

def localColor (T : Tree) : Local → Nat → Nat
  | .keep => fun _ => 0
  | .single v => colorLabel T v
  | .joint v w => jointLabel T v w

def meterLocal (T : Tree) (l : Local) (x : Nat) : Charged Nat :=
  match l with
  | .keep => ⟨0,1⟩
  | .single v => meterColorLabel T v x
  | .joint v w =>
    let a := meterColorLabel T v x
    let b := meterColorLabel T w x
    ⟨4*a.value+b.value,a.work+b.work+3⟩

@[simp] theorem meterLocal_value (T : Tree) (l : Local) (x : Nat) :
    (meterLocal T l x).value = localColor T l x := by
  cases l <;> simp [meterLocal,localColor,jointLabel]

def localCap (T : Tree) : Local → Nat
  | .keep => 1
  | .single v => colorCap T v
  | .joint v w => colorCap T v+colorCap T w+3

theorem meterLocal_bound (T : Tree) (l : Local) (x : Nat) :
    (meterLocal T l x).work ≤ localCap T l := by
  cases l with
  | keep => exact Nat.le_refl _
  | single v => exact meterColorLabel_bound T v x
  | joint v w =>
    have h1 := meterColorLabel_bound T v x
    have h2 := meterColorLabel_bound T w x
    simp only [meterLocal,localCap]; omega

theorem localColor_le_fifteen (T : Tree) (l : Local) (x : Nat) :
    localColor T l x ≤ 15 := by
  cases l with
  | keep => simp [localColor]
  | single v => exact Nat.le_trans (colorLabel_le_three T v x) (by decide)
  | joint v w =>
    have h1 := colorLabel_le_three T v x
    have h2 := colorLabel_le_three T w x
    simp only [localColor,jointLabel]; omega

structure Colors where
  a : Local
  b : Local
  c : Local
  deriving Repr

def colors (T : Tree) (A B : List Nat) (c : Colors) : Nat → Nat :=
  taggedColor A B (localColor T c.a) (localColor T c.b) (localColor T c.c)

def meterTagged (T : Tree) (A B : List Nat) (c : Colors) (x : Nat) : Charged Nat :=
  let a := meterContains x A
  if a.value then
    let l := meterLocal T c.a x
    ⟨3*l.value,a.work+l.work+4⟩
  else
    let b := meterContains x B
    if b.value then
      let l := meterLocal T c.b x
      ⟨3*l.value+1,a.work+b.work+l.work+6⟩
    else
      let l := meterLocal T c.c x
      ⟨3*l.value+2,a.work+b.work+l.work+6⟩

@[simp] theorem meterTagged_value (T : Tree) (A B : List Nat) (c : Colors) (x : Nat) :
    (meterTagged T A B c x).value = colors T A B c x := by
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
    simp [meterTagged,meterContains_value,meterLocal_value,colors,taggedColor,ha,hb]

def taggedCap (T : Tree) (A B : List Nat) (c : Colors) : Nat :=
  4*(A.length+1)+4*(B.length+1)+localCap T c.a+localCap T c.b+localCap T c.c+6

theorem meterTagged_bound (T : Tree) (A B : List Nat) (c : Colors) (x : Nat) :
    (meterTagged T A B c x).work ≤ taggedCap T A B c := by
  have ha := meterContains_bound x A
  have hb := meterContains_bound x B
  have hla := meterLocal_bound T c.a x
  have hlb := meterLocal_bound T c.b x
  have hlc := meterLocal_bound T c.c x
  unfold taggedCap
  by_cases ha' : x ∈ A <;> by_cases hb' : x ∈ B <;>
    simp [meterTagged,meterContains_value,ha',hb'] <;> omega

theorem colors_le_fortyseven (T : Tree) (A B : List Nat) (c : Colors) (x : Nat) :
    colors T A B c x ≤ 47 := by
  have ha := localColor_le_fifteen T c.a x
  have hb := localColor_le_fifteen T c.b x
  have hc := localColor_le_fifteen T c.c x
  unfold colors taggedColor
  split <;> try omega
  split <;> omega

end Universal233.WholeSourceWork
