import PendantMinimal
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork

def eqAddressMeter : RMAF.Vertex→RMAF.Vertex→Measured Bool
 | [],[]=>⟨true,1⟩
 | [],_::_=>⟨false,1⟩
 | _::_,[]=>⟨false,1⟩
 | x::xs,y::ys=>if x==y then let r:=eqAddressMeter xs ys;⟨r.value,r.work+2⟩ else ⟨false,2⟩

theorem eq_address_value (p q : RMAF.Vertex) : (eqAddressMeter p q).value=(p==q) := by
 induction p generalizing q with
 | nil=>cases q <;> rfl
 | cons x xs ih=>cases q with
   | nil=>rfl
   | cons y ys=>simp only [eqAddressMeter,List.cons_beq_cons];split <;> simp_all

theorem eq_address_work (p q : RMAF.Vertex) : (eqAddressMeter p q).work≤p.length+q.length+1 := by
 induction p generalizing q with
 | nil=>cases q <;> simp [eqAddressMeter]
 | cons x xs ih=>cases q with
   | nil=>simp [eqAddressMeter]
   | cons y ys=>have h:=ih ys;simp only [eqAddressMeter];split <;> simp only [List.length_cons] <;> omega

def containsAddressMeter (p : RMAF.Vertex) : List RMAF.Vertex→Measured Bool
 | []=>⟨false,1⟩
 | q::qs=>let c:=eqAddressMeter p q
           if c.value then ⟨true,c.work+1⟩ else let r:=containsAddressMeter p qs;⟨r.value,c.work+r.work+1⟩

theorem contains_address_value (p : RMAF.Vertex) (vs : List RMAF.Vertex) :
 (containsAddressMeter p vs).value=vs.contains p := by
 induction vs with
 | nil=>rfl
 | cons q qs ih=>simp only [containsAddressMeter,eq_address_value,List.contains_cons];split <;> simp_all

theorem contains_address_work (p : RMAF.Vertex) (vs : List RMAF.Vertex) (N : Nat)
 (hp : p.length≤N) (hvs : ∀q,q∈vs →q.length≤N) :
 (containsAddressMeter p vs).work≤(2*N+2)*vs.length+1 := by
 induction vs with
 | nil=>simp [containsAddressMeter]
 | cons q qs ih=>
   have c:=eq_address_work p q
   have tail:=ih (fun r hr=>hvs r (by simp [hr]))
   have head:=hvs q (by simp)
   simp only [containsAddressMeter]
   split <;> (try dsimp only) <;> simp only [List.length_cons,Nat.mul_succ] <;> omega

def dropLastMeter : RMAF.Vertex→Measured RMAF.Vertex
 | []=>⟨[],1⟩
 | [_]=>⟨[],1⟩
 | x::y::xs=>let r:=dropLastMeter (y::xs);⟨x::r.value,r.work+2⟩

theorem drop_last_value (p : RMAF.Vertex) : (dropLastMeter p).value=p.dropLast := by
 induction p with
 | nil=>rfl
 | cons x xs ih=>cases xs with
   | nil=>rfl
   | cons y ys=>simpa only [dropLastMeter,List.dropLast_cons_cons] using congrArg (x::·) ih

theorem drop_last_work (p : RMAF.Vertex) : (dropLastMeter p).work≤2*p.length+1 := by
 induction p with
 | nil=>simp [dropLastMeter]
 | cons x xs ih=>cases xs with
   | nil=>simp [dropLastMeter]
   | cons y ys=>simp only [dropLastMeter,List.length_cons] at *;omega
end Universal233.Rule5PendantLocalWork
