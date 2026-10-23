import AdmittedEnvelope
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

/-- Literal incident predicate, including both occurrences of minimalVertices.
The empty original root takes the actual left short-circuit refusal. -/
def incidentAtMeter (T : Tree) (X : List Nat) (q : RMAF.Vertex) : Measured Bool :=
 if q.isEmpty then ⟨false,1⟩ else
  let m:=minimalMeter X T;let c:=containsAddressMeter q m.value
  let n:=minimalMeter X T;let p:=dropLastMeter q;let d:=containsAddressMeter p.value n.value
  ⟨c.value != d.value,m.work+c.work+n.work+p.work+d.work+4⟩

theorem incident_at_value (T : Tree) (X : List Nat) (q : RMAF.Vertex) :
 (incidentAtMeter T X q).value=(!q.isEmpty &&
  ((minimalVertices X T).contains q != (minimalVertices X T).contains q.dropLast)) := by
 cases q <;> simp only [incidentAtMeter,List.isEmpty_nil,List.isEmpty_cons,Bool.false_eq_true,
   ↓reduceIte,Bool.not_true,Bool.false_and,Bool.not_false,Bool.true_and,
   contains_address_value,minimal_value,drop_last_value]

def incidentAtBudget (k n : Nat) :=2*minimalBudget k n+2*((2*n+2)*(2*n)+1)+2*n+5

theorem incident_at_work (T : Tree) (X : List Nat) (q : RMAF.Vertex)
 (cap : q.length≤(leaves T).length) :
 (incidentAtMeter T X q).work≤incidentAtBudget X.length (leaves T).length := by
 have m:=minimal_work X T
 have mc:=minimal_count X T
 have vc:=vertices_count T
 have ml : (minimalMeter X T).value.length≤2*(leaves T).length := by rw [minimal_value];omega
 have ma : ∀p,p∈(minimalMeter X T).value →p.length≤(leaves T).length := by
  intro p hp;have:=minimal_address X T hp;omega
 have ca:=contains_address_work q (minimalMeter X T).value (leaves T).length cap ma
 have dp : q.dropLast.length≤(leaves T).length := by simp only [List.length_dropLast];omega
 have cb:=contains_address_work q.dropLast (minimalMeter X T).value (leaves T).length dp ma
 have d:=drop_last_work q
 have slots:=Nat.mul_le_mul_left (2*(leaves T).length+2) ml
 simp only [incidentAtMeter]
 split
 · dsimp only;unfold incidentAtBudget;omega
 · dsimp only
   rw [drop_last_value] at *
   unfold incidentAtBudget
   omega

def incidentFilterMeter (T : Tree) (X : List Nat) : List RMAF.Vertex→Measured (List RMAF.Vertex)
 | []=>⟨[],1⟩
 | q::qs=>let c:=incidentAtMeter T X q;let r:=incidentFilterMeter T X qs
           ⟨if c.value then q::r.value else r.value,c.work+r.work+2⟩

theorem incident_filter_value (T : Tree) (X : List Nat) (qs : List RMAF.Vertex) :
 (incidentFilterMeter T X qs).value=qs.filter (fun q=>!q.isEmpty &&
  ((minimalVertices X T).contains q != (minimalVertices X T).contains q.dropLast)) := by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>simp only [incidentFilterMeter,List.filter_cons,incident_at_value,ih]

theorem incident_filter_work (T : Tree) (X : List Nat) (qs : List RMAF.Vertex)
 (cap : ∀q,q∈qs →q.length≤(leaves T).length) :
 (incidentFilterMeter T X qs).work≤(incidentAtBudget X.length (leaves T).length+2)*qs.length+1 := by
 induction qs with
 | nil=>simp [incidentFilterMeter]
 | cons q qs ih=>
  have c:=incident_at_work T X q (cap q (by simp))
  have r:=ih (fun p hp=>cap p (by simp [hp]))
  simp only [incidentFilterMeter,List.length_cons,Nat.mul_succ]
  omega

def incidentMeter (T : Tree) (X : List Nat) : Measured (List RMAF.Vertex) :=
 let v:=verticesMeter T;let r:=incidentFilterMeter T X v.value
 ⟨r.value,v.work+r.work+1⟩

theorem incident_value (T : Tree) (X : List Nat) :
 (incidentMeter T X).value=Rule5Local.incident T X := by
 simp only [incidentMeter,incident_filter_value,vertices_value,Rule5Local.incident]

def incidentBudget (k n : Nat) :=64*n*n+(incidentAtBudget k n+2)*(2*n)+2

theorem incident_work (T : Tree) (X : List Nat) :
 (incidentMeter T X).work≤incidentBudget X.length (leaves T).length := by
 have v:=vertices_work T
 have vc:=vertices_count T
 have filter:=incident_filter_work T X (verticesMeter T).value (by
  intro p hp;have:=vertices_address T hp;omega)
 have slots:=Nat.mul_le_mul_left (incidentAtBudget X.length (leaves T).length+2)
  (show (verticesMeter T).value.length≤2*(leaves T).length by rw [vertices_value];omega)
 simp only [incidentMeter,incidentBudget]
 omega

theorem incident_domain (T : Tree) (X : List Nat) :
 (incidentMeter T X).value.length≤2*(leaves T).length ∧
 ∀q,q∈(incidentMeter T X).value →q.length+1≤(leaves T).length := by
 rw [incident_value]
 have count:=List.length_filter_le (fun q=>!q.isEmpty &&
  ((minimalVertices X T).contains q != (minimalVertices X T).contains q.dropLast)) (vertices T)
 have vc:=vertices_count T
 refine ⟨by unfold Rule5Local.incident;omega,?_⟩
 intro q hq
 apply vertices_address T
 rw [vertices_value]
 exact (List.mem_filter.1 hq).1
end Universal233.Rule5PendantLocalWork
