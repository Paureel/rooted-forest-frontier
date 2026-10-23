/- Delete endpoint b and rename a to fresh z; this handles separate endpoint blocks. -/
import ActualExpansion
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

def shrinkBlock (a b z : Nat) (B : List Nat) : List Nat :=
 (B.filter (fun x=>x != b)).map (fun x=>if x==a then z else x)

def prune (a b z : Nat) : Tree → Option Tree
 | .leaf x => if x==b then none else some (.leaf (if x==a then z else x))
 | .node l r => merge (prune a b z l) (prune a b z r)

def pruneOption (a b z : Nat) (t : Option Tree) := t.bind (prune a b z)

inductive MaybeIso : Option Tree → Option Tree → Prop where
 | none : MaybeIso none none
 | some {T U} : RootedIso T U → MaybeIso (some T) (some U)

theorem merge_iso {l r L R : Option Tree} (hl : MaybeIso l L) (hr : MaybeIso r R) :
 MaybeIso (merge l r) (merge L R) := by
 cases hl <;> cases hr
 · exact .none
 · exact .some (by assumption)
 · exact .some (by assumption)
 · exact .some (.straight (by assumption) (by assumption))

theorem merge_iso_swap {l r L R : Option Tree} (hl : MaybeIso l R) (hr : MaybeIso r L) :
 MaybeIso (merge l r) (merge L R) := by
 cases hl <;> cases hr
 · exact .none
 · exact .some (by assumption)
 · exact .some (by assumption)
 · exact .some (.swapped (by assumption) (by assumption))

theorem prune_iso {T U : Tree} (iso : RootedIso T U) (a b z : Nat) :
 MaybeIso (prune a b z T) (prune a b z U) := by
 induction iso with
 | leaf x =>
  simp only [prune]
  split
  · exact .none
  · exact .some (.leaf _)
 | straight hl hr il ir => exact merge_iso il ir
 | swapped hl hr il ir => exact merge_iso_swap il ir

theorem shrink_fixed_contains (B : List Nat) {a b z x : Nat}
 (xa : x≠a) (xb : x≠b) (xz : x≠z) :
 (shrinkBlock a b z B).contains x=B.contains x := by
 apply Bool.eq_iff_iff.2
 simp only [List.contains_iff_mem,shrinkBlock,List.mem_map,List.mem_filter,Bool.not_eq_true',bne_iff_ne]
 constructor
 · rintro ⟨y,⟨hy,yb⟩,he⟩
   by_cases ya : y=a
   · simp [ya] at he
     exact False.elim (xz he.symm)
   · have yx : y=x := by simpa [ya] using he
     exact yx ▸ hy
 · intro hx
   exact ⟨x,⟨hx,by simpa using xb⟩,by simp [xa]⟩

theorem shrink_z_contains (B : List Nat) {a b z : Nat}
 (ab : a≠b) (nz : z∉B) : (shrinkBlock a b z B).contains z=B.contains a := by
 apply Bool.eq_iff_iff.2
 simp only [List.contains_iff_mem,shrinkBlock,List.mem_map,List.mem_filter,bne_iff_ne]
 constructor
 · rintro ⟨y,⟨hy,_⟩,he⟩
   by_cases ya : y=a
   · exact ya ▸ hy
   · have yz : y=z := by simpa [ya] using he
     exact False.elim (nz (yz ▸ hy))
 · intro ha
   exact ⟨a,⟨ha,by simpa using ab⟩,by simp⟩

theorem prune_merge (a b z : Nat) (l r : Option Tree) :
 pruneOption a b z (merge l r)=merge (pruneOption a b z l) (pruneOption a b z r) := by
 have mn : ∀t,merge t none=t := by intro t;cases t <;> rfl
 have nm : ∀t,merge none t=t := by intro t;cases t <;> rfl
 cases l <;> cases r <;> simp only [merge,pruneOption,Option.bind_none,Option.bind_some,prune] <;> first | rfl | exact (mn _).symm | exact (nm _).symm

theorem restrict_shrink {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (ab : a≠b) (B : List Nat) (nz : z∉B) :
 restrict (shrinkBlock a b z B) C=pruneOption a b z (restrict B T) := by
 induction h with
 | fixed xa xb xz =>
  have sf : _∈shrinkBlock a b z B ↔ _∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 (shrink_fixed_contains B xa xb xz)
  simp [restrict,sf,pruneOption,prune,xa,xb]
  split <;> simp [prune,xa,xb]
 | cherry =>
  have sz := shrink_z_contains B ab nz
  have sm : z∈shrinkBlock a b z B ↔ a∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 sz
  by_cases ha : a∈B <;> by_cases hb : b∈B <;>
   simp [restrict,sm,ha,hb,pruneOption,prune,merge,ab]
 | swapped =>
  have sz := shrink_z_contains B ab nz
  have sm : z∈shrinkBlock a b z B ↔ a∈B := by simpa only [List.contains_iff_mem] using Bool.eq_iff_iff.1 sz
  by_cases ha : a∈B <;> by_cases hb : b∈B <;>
   simp [restrict,sm,ha,hb,pruneOption,prune,merge,ab]
 | node hl hr il ir =>
  change merge _ _=pruneOption a b z (merge _ _)
  rw [prune_merge,il,ir]
end IndependentGeometry
