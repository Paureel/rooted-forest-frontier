import Work

/-! Auditable source-operation charge identities. Scalar Nat equality/addition
is one operation here; address equality is charged by inspected list capacity.
The RAM/bit conversion and full per-prefix charge sheet are COST-MODEL.md. -/
namespace Universal233.CoreWork
open RMAF CoreProgram

def gNodes : GTree → Nat
  | .leaf _ => 1
  | .node _ l r => 1+gNodes l+gNodes r

theorem gNodes_le (t : GTree) : gNodes t ≤ footprint t := by
  induction t with
  | leaf g => simp only [gNodes,footprint]; omega
  | node p l r ihl ihr => simp only [gNodes,footprint]; omega

/-- Charged recursive matches/allocations and literal left cells in groups ++. -/
def groupsWork : GTree → Nat
  | .leaf _ => 2
  | .node _ l r => groupsWork l+groupsWork r+5+(groups l).length

theorem groupsWork_bound (t : GTree) (s : Nat) (h : footprint t ≤ s) :
    groupsWork t ≤ (s+5)*gNodes t := by
  induction t with
  | leaf g => simp only [groupsWork,gNodes,Nat.mul_one]; omega
  | node p l r ihl ihr =>
    have hl : footprint l ≤ s := by simp only [footprint] at h; omega
    have hr : footprint r ≤ s := by simp only [footprint] at h; omega
    have hgl := groups_length l
    have bl := ihl hl
    have br := ihr hr
    simp only [groupsWork,gNodes,Nat.mul_add,Nat.mul_one]
    omega

/-- Match/equality/allocation charge plus actual label cells copied at each
homogeneous contraction. No unit-time unbounded label append is assumed. -/
def normalizeWork : GTree → Nat
  | .leaf _ => 1
  | .node _ l r => normalizeWork l+normalizeWork r+8+
      match normalize l,normalize r with
      | .leaf a,.leaf b => if a.color = b.color then a.labels.length else 0
      | _,_ => 0

theorem normalizeWork_bound (t : GTree) (s : Nat) (h : footprint t ≤ s) :
    normalizeWork t ≤ (s+8)*gNodes t := by
  induction t with
  | leaf g => simp only [normalizeWork,gNodes,Nat.mul_one]; omega
  | node p l r ihl ihr =>
    have hl : footprint l ≤ s := by simp only [footprint] at h; omega
    have hr : footprint r ≤ s := by simp only [footprint] at h; omega
    have bl := ihl hl
    have br := ihr hr
    have hn := normalize_footprint l
    simp only [normalizeWork,gNodes,Nat.mul_add,Nat.mul_one]
    cases hal : normalize l with
    | leaf a =>
      simp only [hal,footprint] at hn
      cases hbr : normalize r <;> simp only
      · split <;> omega
      · omega
    | node q a b => cases hbr : normalize r <;> simp only <;> omega

/-- Full-tree upper traversal for erase, including every original-address
comparison and both recursive subcalls. Early deletion only reduces this. -/
def eraseWork (v : Vertex) : GTree → Nat
  | .leaf g => v.length+g.origin.length+8
  | .node p l r => eraseWork v l+eraseWork v r+v.length+p.length+8

theorem eraseWork_bound (v : Vertex) (t : GTree) (s : Nat)
    (ht : footprint t ≤ s) (hv : v.length ≤ s) :
    eraseWork v t ≤ (2*s+8)*gNodes t := by
  induction t with
  | leaf g => simp only [eraseWork,gNodes,Nat.mul_one,footprint] at *; omega
  | node p l r ihl ihr =>
    have hl : footprint l ≤ s := by simp only [footprint] at ht; omega
    have hr : footprint r ≤ s := by simp only [footprint] at ht; omega
    have bl := ihl hl
    have br := ihr hr
    simp only [eraseWork,gNodes,Nat.mul_add,Nat.mul_one,footprint] at *
    omega

/-- Predicate charge includes filter's traversal+allocation, its output length
traversal, equality to 1, and find's own list traversal. It conservatively uses
full list capacity for each candidate but retains the actual stopping guard. -/
def findFilterWork (gs : List Group) : List Group → Nat
  | [] => 1
  | g::rest => 8*(gs.length+1)+2+
      if (gs.filter (fun h => h.color == g.color)).length == 1 then 0
      else findFilterWork gs rest

theorem findFilterWork_bound (gs xs : List Group) :
    findFilterWork gs xs ≤ (8*(gs.length+1)+2)*xs.length+1 := by
  induction xs with
  | nil => simp [findFilterWork]
  | cons g xs ih =>
    simp only [findFilterWork,List.length_cons,Nat.mul_add,Nat.mul_one] at ih ⊢
    split <;> omega

def allWork (color : Nat) : List Group → Nat
  | [] => 1
  | g::rest => 2 + if g.color == color then allWork color rest else 0

theorem allWork_bound (color : Nat) (gs : List Group) :
    allWork color gs ≤ 2*gs.length+1 := by
  induction gs with
  | nil => simp [allWork]
  | cons g gs ih =>
    simp only [allWork,List.length_cons,Nat.mul_add,Nat.mul_one]
    split <;> omega

/-- Worst-case charged mixedCherry traversal. Both arguments of Option.or may
be evaluated; the bound does not depend on compiler short-circuiting. -/
def mixedWork (t : GTree) : Nat := 4*gNodes t

/-- Source-local charge sheet after applying the helper bounds, with s current
constructor/payload/address capacity, a detached count and b cut count. It
covers both attempted children and output construction even when unused. -/
def sourceLocalMajorant (s a b : Nat) : Nat :=
  (s+8)*s + ((s+5)*s + (8*(s+1)+2)*s + 2*s+1 + 4*s+16) +
  2*((b+1)*(s+1)+(2*s+8)*s+8) + ((s+5)*s+8*(s+a+1)) + 24

/-- Polynomial domination is deliberately roomy; the exact helper work is
smaller and list append cells at recursive returns remain charged separately. -/
theorem sourceLocalMajorant_bound (s a b : Nat) :
    sourceLocalMajorant s a b ≤ 128*(s+a+b+1)^3 := by
  let r := s+a+b+1
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hs : s ≤ r := by dsimp [r]; omega
  have ha : s+a+1 ≤ r := by dsimp [r]; omega
  have hb : b+1 ≤ r := by dsimp [r]; omega
  have hs1 : s+1 ≤ r := by dsimp [r]; omega
  have hs8 : s+8 ≤ 9*r := by omega
  have hs5 : s+5 ≤ 6*r := by omega
  have hs28 : 2*s+8 ≤ 10*r := by omega
  have hs82 : 8*(s+1)+2 ≤ 10*r := by omega
  have h1 := Nat.mul_le_mul hs8 hs
  have h2 := Nat.mul_le_mul hs5 hs
  have h3 := Nat.mul_le_mul hs28 hs
  have h4 := Nat.mul_le_mul hs82 hs
  have h5 := Nat.mul_le_mul hb hs1
  have hrr : r ≤ r*r := by simpa using Nat.mul_le_mul_left r hr
  have hrrr : r*r ≤ r*r*r := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (r*r) hr
  simp only [Nat.mul_assoc] at h1 h2 h3 h4
  unfold sourceLocalMajorant
  change _ ≤ 128*r^3
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul,Nat.mul_one]
  omega


theorem payload_length (t : GTree) : (payload t).length ≤ footprint t := by
  induction t with
  | leaf g => simp only [payload,footprint]; omega
  | node p l r ihl ihr => simp only [payload,List.length_append,footprint]; omega

theorem groups_flatMap_payload (t : GTree) :
    (groups t).flatMap Group.labels = payload t := by
  induction t with
  | leaf g => simp [groups,payload]
  | node p l r ihl ihr => simp only [groups,payload,List.flatMap_append,ihl,ihr]

theorem primitive_sheet_le_localCharge (t : GTree) (d : List Group) (c : List Vertex) :
    sourceLocalMajorant (footprint t) d.length c.length ≤ localCharge t d c :=
  sourceLocalMajorant_bound _ _ _

end Universal233.CoreWork
