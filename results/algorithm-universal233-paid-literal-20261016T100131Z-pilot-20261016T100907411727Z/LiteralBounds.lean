import LiteralDecision
namespace Universal233.PaidLiteralDecisionWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork
open Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard Case322Extraction

theorem square_mono (n N : Nat) (h : n≤N) : n*n≤N*N := Nat.mul_le_mul h h

theorem minimal_budget_mono (k n K N : Nat) (hk : k≤K) (hn : n≤N) :
 minimalBudget k n≤minimalBudget K N := by
 have a:=Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hk 1)) hn) hn
 have b:=Nat.mul_le_mul_left 16 hn
 exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) (by omega)

theorem incident_at_budget_mono (k n K N : Nat) (hk : k≤K) (hn : n≤N) :
 incidentAtBudget k n≤incidentAtBudget K N := by
 have a:=minimal_budget_mono k n K N hk hn
 have b:=Nat.mul_le_mul (show 2*n+2≤2*N+2 by omega) (Nat.mul_le_mul_left 2 hn)
 unfold incidentAtBudget;omega

theorem incident_budget_mono (k n K N : Nat) (hk : k≤K) (hn : n≤N) :
 incidentBudget k n≤incidentBudget K N := by
 have a:=incident_at_budget_mono k n K N hk hn
 have b:=Nat.mul_le_mul (Nat.add_le_add_right a 2) (Nat.mul_le_mul_left 2 hn)
 have c:=Nat.mul_le_mul_left 64 (square_mono n N hn)
 unfold incidentBudget
 simp only [Nat.mul_assoc] at *
 omega

theorem cuts_budget_mono (n N : Nat) (hn : n≤N) : cutsBudget n≤cutsBudget N := by
 have a:=minimal_budget_mono 2 n 2 N (Nat.le_refl 2) hn
 have b:=Nat.mul_le_mul (show 2*n+2≤2*N+2 by omega) (Nat.mul_le_mul_left 2 hn)
 have c : cutGuardBudget n≤cutGuardBudget N := by unfold cutGuardBudget;omega
 have d:=Nat.mul_le_mul (Nat.add_le_add_right c 2) (Nat.mul_le_mul_left 2 hn)
 have e:=Nat.mul_le_mul_left 64 (square_mono n N hn)
 unfold cutsBudget
 simp only [Nat.mul_assoc] at *
 omega

theorem cherry_budget_mono (n N : Nat) (hn : n≤N) : cherryBudget n≤cherryBudget N := by
 have a:=Nat.mul_le_mul (show 4*n+26≤4*N+26 by omega) (Nat.mul_le_mul_left 2 hn)
 have b:=Nat.mul_le_mul_left 64 (square_mono n N hn)
 unfold cherryBudget
 simp only [Nat.mul_assoc] at *
 omega

theorem labels_budget_mono (nt nc nx N : Nat) (ht : nt≤N) (hc : nc≤N) (hx : nx≤N) :
 labelsBudget nt nc nx≤labelsBudget N N N := by
 have t:=Nat.mul_le_mul_left 4 (square_mono nt N ht)
 have c:=Nat.mul_le_mul_left 4 (square_mono nc N hc)
 have x:=Nat.mul_le_mul_left 4 (square_mono nx N hx)
 have p : labelPointBudget nc nx≤labelPointBudget N N := by
  unfold labelPointBudget
  simp only [Nat.mul_assoc] at *
  omega
 have z:=Nat.mul_le_mul (Nat.add_le_add_right p 1) ht
 unfold labelsBudget
 simp only [Nat.mul_assoc] at *
 omega

def membershipBudget (N : Nat) :=4*N*N+2*N+2

theorem membership_work (T : Tree) (z N : Nat) (h : (leaves T).length≤N) :
 (containsTreeMeter T z).work≤membershipBudget N := by
 have a:=contains_tree_work T z
 have b:=Nat.mul_le_mul_left 4 (square_mono _ N h)
 unfold membershipBudget
 simp only [Nat.mul_assoc] at *
 omega

def minMemBudget (N : Nat) :=4*N*N+minimalBudget N N+(2*N+2)*(2*N)+3

theorem minimal_mem_work (T X : Tree) (q : RMAF.Vertex) (N : Nat)
 (ht : (leaves T).length≤N) (hx : (leaves X).length≤N) (hq : q.length≤N) :
 (minimalMemMeter T X q).work≤minMemBudget N := by
 have x:=leaves_work X
 have xx:=Nat.mul_le_mul_left 4 (square_mono _ N hx)
 have m:=minimal_work (leaves X) T
 have mm:=minimal_budget_mono (leaves X).length (leaves T).length N N hx ht
 have count : (minimalMeter (leaves X) T).value.length≤2*N := by
  have a:=minimal_count (leaves X) T;have b:=vertices_count T
  rw [minimal_value];omega
 have c:=contains_address_work q (minimalMeter (leaves X) T).value N hq (by
  intro p hp;have a:=minimal_address (leaves X) T hp;omega)
 have cc:=Nat.mul_le_mul_left (2*N+2) count
 simp only [minimalMemMeter,leaves_value,minMemBudget]
 simp only [Nat.mul_assoc] at *
 omega

def tailMemBudget (N : Nat) :=2*N+minMemBudget N+2

theorem tail_mem_work (T X : Tree) (q : RMAF.Vertex) (N : Nat)
 (ht : (leaves T).length≤N) (hx : (leaves X).length≤N) (hq : q.length≤N) :
 (tailMemMeter T X q).work≤tailMemBudget N := by
 have d:=drop_last_work q
 have dp : (dropLastMeter q).value.length≤N := by rw [drop_last_value,List.length_dropLast];omega
 have m:=minimal_mem_work T X (dropLastMeter q).value N ht hx dp
 simp only [tailMemMeter,tailMemBudget];omega

def incidentEqBudget (N : Nat) :=4*N*N+incidentBudget N N+(2*N+3)*2+4

theorem incident_eq_work (T X : Tree) (u v : RMAF.Vertex) (N : Nat)
 (ht : (leaves T).length≤N) (hx : (leaves X).length≤N) (hu : u.length≤N) (hv : v.length≤N) :
 (incidentEqMeter T X u v).work≤incidentEqBudget N := by
 have x:=leaves_work X
 have xx:=Nat.mul_le_mul_left 4 (square_mono _ N hx)
 have i:=incident_work T (leaves X)
 have ii:=incident_budget_mono (leaves X).length (leaves T).length N N hx ht
 have e:=list_eq_work eqAddressMeter [v,u] (incidentMeter T (leaves X)).value (2*N+1) (by
  intro p hp q hq
  have pp : p=v ∨ p=u := by simpa using hp
  have pd : p.length≤N := by rcases pp with rfl|rfl <;> assumption
  have qd:= (incident_domain T (leaves X)).2 q hq
  have ee:=eq_address_work p q
  omega)
 simp only [List.length_cons,List.length_nil,Nat.reduceAdd] at e
 simp only [incidentEqMeter,leaves_value,incidentEqBudget,addressListsEqMeter]
 simp only [Nat.mul_assoc] at *
 omega

def boundaryBudget (N : Nat) :=8*N*N+5*N+7

theorem boundary_eq_work (S X : Tree) (p : RMAF.Vertex) (N : Nat)
 (hs : (leaves S).length≤N) (hx : (leaves X).length≤N) (hp : p.length≤N) :
 (boundaryEqMeter S X p).work≤boundaryBudget N := by
 have s:=subtree_labels_work S p
 have sp:=subtree_labels_payload S p
 have x:=leaves_work X
 have e:=nat_list_eq_work (subtreeLabelsMeter S p).value (leavesMeter X).value
 have ss:=Nat.mul_le_mul_left 4 (square_mono _ N hs)
 have xx:=Nat.mul_le_mul_left 4 (square_mono _ N hx)
 simp only [boundaryEqMeter,boundaryBudget]
 simp only [Nat.mul_assoc] at *
 omega

/-- An explicit polynomial in N, containing every repeated occurrence. -/
def literalBudget (N : Nat) :=
 properPolynomial N+(8*N+31)+cherryBudget N+(cutsBudget N+2*N+3)+labelsBudget N N N+
 2*membershipBudget N+1+3*(2*N+6)+(2*incidentEqBudget N+1)+
 2*tailMemBudget N+2*(minMemBudget N+1)+boundaryBudget N+9+18

end Universal233.PaidLiteralDecisionWork
