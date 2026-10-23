import PendantSpan
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork

def minimalMeter (D : List Nat) : Tree→Measured (List RMAF.Vertex)
 | .leaf x=>let c:=containsMeter x D;⟨if c.value then [[]] else [],c.work+2⟩
 | .node l r=>let a:=spanMeter D l;let b:=spanMeter D r
               if a.value.isEmpty then
                let m:=minimalMeter D r
                ⟨prependSide true m.value,a.work+b.work+m.work+4*m.value.length+3⟩
               else if b.value.isEmpty then
                let m:=minimalMeter D l
                ⟨prependSide false m.value,a.work+b.work+m.work+4*m.value.length+3⟩
               else ⟨[]::(prependSide false a.value++prependSide true b.value),
                 a.work+b.work+6*a.value.length+5*b.value.length+3⟩

theorem minimal_value (D : List Nat) (T : Tree) : (minimalMeter D T).value=minimalVertices D T := by
 induction T with
 | leaf x=>simp only [minimalMeter,minimalVertices,contains_value]
 | node l r hl hr=>simp only [minimalMeter,minimalVertices,span_value];split <;> (try split) <;> simp only [hl,hr]

theorem minimal_count (D : List Nat) (T : Tree) : (minimalVertices D T).length≤(vertices T).length := by
 induction T with
 | leaf x=>simp only [minimalVertices];split <;> simp [vertices]
 | node l r hl hr=>
   have lc:=span_count D l
   have rc:=span_count D r
   simp only [minimalVertices]
   split <;> (try split) <;> simp only [vertices,prependSide,List.length_cons,List.length_append,List.length_map] <;> omega

theorem minimal_address (D : List Nat) (T : Tree) {p : RMAF.Vertex} (mem : p∈(minimalMeter D T).value) :
 p.length+1≤(leaves T).length := by
 rw [minimal_value] at mem
 obtain ⟨U,sub⟩:=Integration.minimalVertices_actual D T p mem
 exact subtree_depth sub

theorem one_child_bill (m own count N B : Nat) (rec : m≤count*B) (local : own≤B)
 (slots : count+1≤N) : m+own≤N*B := by
 have h:=Nat.mul_le_mul_right B slots
 rw [Nat.add_mul,Nat.one_mul] at h
 omega

theorem minimal_work_structural (D : List Nat) (T : Tree) :
 (minimalMeter D T).work≤(vertices T).length*spanCharge D T := by
 induction T with
 | leaf x=>simp only [minimalMeter,vertices,spanCharge,spanMeter,List.length_cons,List.length_nil,Nat.one_mul];omega
 | node l r hl hr=>
   have vc : (vertices (.node l r)).length=(vertices l).length+(vertices r).length+1 := by
     simp only [vertices,prependSide,List.length_cons,List.length_append,List.length_map]
   have lower:=span_node_lower D l r
   have bc:=span_charge_child D l r
   have ml:=minimal_count D l
   have mr:=minimal_count D r
   have sl:=span_count D l
   have sr:=span_count D r
   have il:=Nat.le_trans hl (Nat.mul_le_mul_left (vertices l).length bc.1)
   have ir:=Nat.le_trans hr (Nat.mul_le_mul_left (vertices r).length bc.2)
   have ownl : (spanMeter D l).work+(spanMeter D r).work+4*(minimalMeter D l).value.length+3≤spanCharge D (.node l r) := by
     rw [minimal_value]
     unfold spanCharge
     rw [vc]
     omega
   have ownr : (spanMeter D l).work+(spanMeter D r).work+4*(minimalMeter D r).value.length+3≤spanCharge D (.node l r) := by
     rw [minimal_value]
     unfold spanCharge
     rw [vc]
     omega
   have left:=one_child_bill _ _ _ _ _ il ownl (by rw [vc];omega)
   have right:=one_child_bill _ _ _ _ _ ir ownr (by rw [vc];omega)
   have full : (spanMeter D l).work+(spanMeter D r).work+6*(spanMeter D l).value.length+5*(spanMeter D r).value.length+3≤spanCharge D (.node l r) := by
     rw [span_value,span_value]
     unfold spanCharge
     rw [vc]
     omega
   have whole : spanCharge D (.node l r)≤(vertices (.node l r)).length*spanCharge D (.node l r) := by
     have:=Nat.mul_le_mul_right (spanCharge D (.node l r)) (vertices_positive (.node l r))
     simpa using this
   simp only [minimalMeter]
   split <;> (try split) <;> (try dsimp only) <;> omega

def minimalBudget (k n : Nat) : Nat := 2*n*(64*(k+1)*n*n+16*n+4)

theorem minimal_work (D : List Nat) (T : Tree) :
 (minimalMeter D T).work≤minimalBudget D.length (leaves T).length := by
 have m:=minimal_work_structural D T
 have s:=span_work D T
 have v:=vertices_count T
 have vb : (vertices T).length≤2*(leaves T).length := by omega
 have base : spanCharge D T≤64*(D.length+1)*(leaves T).length*(leaves T).length+16*(leaves T).length+4 := by
   unfold spanCharge
   omega
 exact Nat.le_trans m (Nat.mul_le_mul vb base)
end Universal233.Rule5PendantLocalWork
