import PendantVertices
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork

def spanMeter (D : List Nat) : Tree→Measured (List RMAF.Vertex)
 | .leaf x=>let c:=containsMeter x D
            ⟨if c.value then [[]] else [],c.work+2⟩
 | .node l r=>let a:=spanMeter D l;let b:=spanMeter D r
               if a.value.isEmpty && b.value.isEmpty then ⟨[],a.work+b.work+2⟩
               else ⟨[]::(prependSide false a.value++prependSide true b.value),
                 a.work+b.work+6*a.value.length+5*b.value.length+3⟩

theorem span_value (D : List Nat) (T : Tree) : (spanMeter D T).value=rootedSpan D T := by
 induction T with
 | leaf x=>simp only [spanMeter,rootedSpan,contains_value]
 | node l r hl hr=>simp only [spanMeter,rootedSpan,hl,hr];split <;> rfl

theorem span_count (D : List Nat) (T : Tree) : (rootedSpan D T).length≤(vertices T).length := by
 induction T with
 | leaf x=>simp only [rootedSpan];split <;> simp [vertices]
 | node l r hl hr=>
   simp only [rootedSpan]
   split <;> simp only [vertices,prependSide,List.length_nil,List.length_cons,List.length_append,List.length_map] <;> omega

theorem span_address (D : List Nat) (T : Tree) {p : RMAF.Vertex} (mem : p∈(spanMeter D T).value) :
 p.length+1≤(leaves T).length := by
 rw [span_value] at mem
 obtain ⟨U,sub⟩:=VertexGeometry.rootedSpan_actual D T p mem
 exact subtree_depth sub

theorem span_work (D : List Nat) (T : Tree) :
 (spanMeter D T).work≤64*(D.length+1)*(leaves T).length*(leaves T).length := by
 induction T with
 | leaf x=>
   have c:=contains_work x D
   simp only [spanMeter,leaves,List.length_cons,List.length_nil]
   omega
 | node l r hl hr=>
   have lc:=Nat.le_trans (span_count D l) (by have:=vertices_count l;omega : (vertices l).length≤2*(leaves l).length)
   have rc:=Nat.le_trans (span_count D r) (by have:=vertices_count r;omega : (vertices r).length≤2*(leaves r).length)
   have b:=weighted_quadratic (64*(D.length+1)) _ _ _ _ (by omega) (leaves_positive l) (leaves_positive r) hl hr
   simp only [spanMeter,span_value]
   split <;> simp only [leaves,List.length_append] <;> omega

theorem span_node_lower (D : List Nat) (l r : Tree) :
 (spanMeter D l).work+(spanMeter D r).work≤(spanMeter D (.node l r)).work := by
 simp only [spanMeter]
 split <;> (try dsimp only) <;> omega

def spanCharge (D : List Nat) (T : Tree) : Nat := (spanMeter D T).work+8*(vertices T).length+4

theorem span_charge_child (D : List Nat) (l r : Tree) :
 spanCharge D l≤spanCharge D (.node l r) ∧ spanCharge D r≤spanCharge D (.node l r) := by
 have lo:=span_node_lower D l r
 have len : (vertices (.node l r)).length=(vertices l).length+(vertices r).length+1 := by
   simp only [vertices,prependSide,List.length_cons,List.length_append,List.length_map]
 unfold spanCharge
 rw [len]
 omega
end Universal233.Rule5PendantLocalWork
