import ProperPairWork
namespace Universal233.Rule5PrefixLocalWork
open RMAF CherryBranching
abbrev CherryRow := RMAF.Vertex×Nat×Nat

def cherriesMeter : Tree→Measured (List CherryRow)
 | .leaf _=>⟨[],1⟩
 | .node (.leaf a) (.leaf b)=>⟨[([],a,b)],3⟩
 | .node l r=>let a:=cherriesMeter l;let b:=cherriesMeter r
               ⟨a.value.map (fun (p,x,y)=>(false::p,x,y))++
                b.value.map (fun (p,x,y)=>(true::p,x,y)),
                a.work+b.work+6*a.value.length+5*b.value.length+3⟩

theorem cherries_value (T : Tree) : (cherriesMeter T).value=cherries T := by
 induction T with
 | leaf x=>rfl
 | node l r hl hr=>cases l <;> cases r <;> simp only [cherriesMeter,cherries,hl,hr]

theorem cherries_count (T : Tree) : (cherries T).length≤(leaves T).length := by
 induction T with
 | leaf x=>simp [cherries,leaves]
 | node l r hl hr=>
   cases l <;> cases r <;> simp only [cherries,leaves,List.length_append,List.length_map,List.length_cons,List.length_nil] at * <;> omega

theorem cherries_node_charge (l r : Tree) :
 (cherriesMeter (.node l r)).work≤(cherriesMeter l).work+(cherriesMeter r).work+
   6*(cherries l).length+5*(cherries r).length+3 := by
 cases l <;> cases r <;> simp only [cherriesMeter,cherries_value,cherries,List.length_cons,List.length_nil] <;> omega

theorem cherry_quadratic (a b wa wb : Nat) (ha : 1≤a) (hb : 1≤b)
 (hA : wa≤16*a*a) (hB : wb≤16*b*b) : wa+wb+6*a+5*b+3≤16*(a+b)*(a+b) := by
 have crossA : a≤a*b := by have:=Nat.mul_le_mul_left a hb;simpa using this
 have crossB : b≤a*b := by have:=Nat.mul_le_mul_right b ha;simpa using this
 have pos : 1≤a*b := by have:=Nat.mul_le_mul ha hb;simpa using this
 simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
 rw [Nat.mul_comm b a]
 omega

theorem cherries_work (T : Tree) : (cherriesMeter T).work≤16*(leaves T).length*(leaves T).length := by
 induction T with
 | leaf x=>simp [cherriesMeter,leaves]
 | node l r hl hr=>
   have charge:=cherries_node_charge l r
   have cl:=cherries_count l
   have cr:=cherries_count r
   have whole:=cherry_quadratic _ _ _ _ (leaves_positive l) (leaves_positive r) hl hr
   simp only [leaves,List.length_append]
   omega

/-- Four bounded Nat endpoint equalities and Boolean/list/tuple overhead.
Conservative full predicate charge also covers internal early Boolean stops. -/
def endpointGuard (a b : Nat) (c : CherryRow) : Bool :=
 let (_,x,y):=c;(x==a && y==b)||(x==b && y==a)

def cherryAnyMeter (a b : Nat) : List CherryRow→Measured Bool
 | []=>⟨false,1⟩
 | c::cs=>if endpointGuard a b c then ⟨true,8⟩ else
           let r:=cherryAnyMeter a b cs;⟨r.value,r.work+8⟩

theorem cherry_any_value (a b : Nat) (cs : List CherryRow) :
 (cherryAnyMeter a b cs).value=cs.any (endpointGuard a b) := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>simp only [cherryAnyMeter,List.any_cons];split <;> simp_all

theorem cherry_any_work (a b : Nat) (cs : List CherryRow) :
 (cherryAnyMeter a b cs).work≤8*cs.length+1 := by
 induction cs with
 | nil=>simp [cherryAnyMeter]
 | cons c cs ih=>simp only [cherryAnyMeter];split <;> simp only [List.length_cons] <;> omega

def hasCherryMeter (T : Tree) (a b : Nat) : Measured Bool :=
 let c:=cherriesMeter T;let r:=cherryAnyMeter a b c.value
 ⟨r.value,c.work+r.work+1⟩

theorem has_cherry_value (T : Tree) (a b : Nat) :
 (hasCherryMeter T a b).value=Rule5Local.hasCherry T a b := by
 simp only [hasCherryMeter,cherry_any_value,cherries_value,Rule5Local.hasCherry,endpointGuard]

theorem has_cherry_work (T : Tree) (a b : Nat) :
 (hasCherryMeter T a b).work≤16*(leaves T).length*(leaves T).length+8*(leaves T).length+2 := by
 have c:=cherries_work T
 have a:=cherry_any_work a b (cherries T)
 have size:=cherries_count T
 simp only [hasCherryMeter,cherries_value]
 omega

/-- Original unsuppressed address payloads are bounded as data, independent
of nodup/properness and including every enumerated row. -/
theorem subtree_depth {T U : Tree} {p : RMAF.Vertex} (sub : subtree T p=some U) :
 p.length+1≤(leaves T).length := by
 induction T generalizing U p with
 | leaf x=>cases p <;> simp_all [subtree,leaves]
 | node l r hl hr=>
   cases p with
   | nil=>have:=leaves_positive (.node l r);simpa using this
   | cons bit p=>
     have lp:=leaves_positive l
     have rp:=leaves_positive r
     cases bit with
     | false=>have h:=hl (by simpa [subtree] using sub);simp only [List.length_cons,leaves,List.length_append];omega
     | true=>have h:=hr (by simpa [subtree] using sub);simp only [List.length_cons,leaves,List.length_append];omega

theorem cherry_row_payload (T : Tree) (p : RMAF.Vertex) (a b : Nat)
 (mem : (p,a,b)∈(cherriesMeter T).value) :
 p.length+1≤(leaves T).length ∧ a∈leaves T ∧ b∈leaves T := by
 rw [cherries_value] at mem
 have ch:=cherries_sound T p a b mem
 exact ⟨subtree_depth ch,RestrictionBridge.hasCherry_labels (RestrictionBridge.actual_hasCherry ch)⟩
end Universal233.Rule5PrefixLocalWork
