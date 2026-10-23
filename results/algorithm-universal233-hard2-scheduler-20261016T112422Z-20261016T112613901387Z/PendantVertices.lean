import PrefixGuardEnvelope
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork

def verticesMeter : Tree→Measured (List RMAF.Vertex)
 | .leaf _=>⟨[[]],2⟩
 | .node l r=>let a:=verticesMeter l;let b:=verticesMeter r
               ⟨[]::(prependSide false a.value++prependSide true b.value),
               a.work+b.work+5*a.value.length+4*b.value.length+3⟩

theorem vertices_value (T : Tree) : (verticesMeter T).value=vertices T := by
 induction T with
 | leaf x=>rfl
 | node l r hl hr=>simp only [verticesMeter,vertices,hl,hr]

theorem vertices_count (T : Tree) : (vertices T).length+1=2*(leaves T).length := by
 induction T with
 | leaf x=>simp [vertices,leaves]
 | node l r hl hr=>simp only [vertices,leaves,prependSide,List.length_cons,List.length_append,List.length_map];omega

theorem vertices_positive (T : Tree) : 1≤(vertices T).length := by
 have c:=vertices_count T
 have n:=leaves_positive T
 omega

/-- Generic source quadratic composition, paying all map/append/guard cells. -/
theorem weighted_quadratic (C a b wa wb : Nat) (hC : 64≤C) (ha : 1≤a) (hb : 1≤b)
 (hA : wa≤C*a*a) (hB : wb≤C*b*b) : wa+wb+12*a+10*b+3≤C*(a+b)*(a+b) := by
 have crossA : a≤a*b := by have:=Nat.mul_le_mul_left a hb;simpa using this
 have crossB : b≤a*b := by have:=Nat.mul_le_mul_right b ha;simpa using this
 have pos : 1≤a*b := by have:=Nat.mul_le_mul ha hb;simpa using this
 have lower:=Nat.mul_le_mul_right (a*b) hC
 simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
 rw [Nat.mul_comm b a]
 omega

theorem vertices_work (T : Tree) : (verticesMeter T).work≤64*(leaves T).length*(leaves T).length := by
 induction T with
 | leaf x=>simp [verticesMeter,leaves]
 | node l r hl hr=>
   have lc:=vertices_count l
   have rc:=vertices_count r
   have b:=weighted_quadratic 64 _ _ _ _ (by decide) (leaves_positive l) (leaves_positive r) hl hr
   simp only [verticesMeter,vertices_value,leaves,List.length_append]
   omega

theorem vertices_address (T : Tree) {p : RMAF.Vertex} (mem : p∈(verticesMeter T).value) :
 p.length+1≤(leaves T).length := by
 rw [vertices_value] at mem
 obtain ⟨U,sub⟩:=(vertices_correct T p).1 mem
 exact subtree_depth sub
end Universal233.Rule5PendantLocalWork
