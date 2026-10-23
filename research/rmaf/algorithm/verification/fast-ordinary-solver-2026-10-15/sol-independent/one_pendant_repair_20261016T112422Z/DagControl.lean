/- Synthetic truth control for bounded DAG rows, fixed before producer use. -/
def sharedValue (n : Nat) : Nat := n+n
 theorem shared_refl (n : Nat) : sharedValue n=n+n := rfl
 inductive ControlBox where | box : Nat→ControlBox
 def unbox : ControlBox→Nat | .box n=>n
 opaque opaqueN : Nat := 17
 theorem unbox_truth : unbox (.box 23)=23 := rfl
