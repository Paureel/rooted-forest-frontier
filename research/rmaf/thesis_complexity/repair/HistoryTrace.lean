import Std
namespace HistoryTrace
inductive T where
 | leaf : Nat → T
 | fork : T → T → T
 | rho : T → T
 deriving DecidableEq, BEq, Repr
open T
-- Reused generic definitions from the original Trace.lean; this module is a
-- concrete finite witness, not a universal source-state formalization.
def contains (s : T) (i : Nat) : Bool := match s with
 | leaf j => i == j
 | fork l r => contains l i || contains r i
 | rho u => contains u i

def existsSub (s u : T) : Bool := s == u || match s with
 | leaf _ => false
 | fork l r => existsSub l u || existsSub r u
 | rho v => existsSub v u

def parentSub (s u : T) : Option T := match s with
 | leaf _ => none
 | fork l r => if l == u || r == u then some s else (parentSub l u).or (parentSub r u)
 | rho v => if v == u then some s else parentSub v u

def siblingSub (s u : T) : Option T := match s with
 | leaf _ => none
 | fork l r => if l == u then some r else if r == u then some l else (siblingSub l u).or (siblingSub r u)
 | rho v => siblingSub v u

def depth (s : T) (i : Nat) : Nat := match s with
 | leaf _ => 0
 | fork l r => 1 + if contains l i then depth l i else depth r i
 | rho u => 1 + depth u i

def cherries : T → List (Nat × Nat)
 | leaf _ => []
 | fork (leaf i) (leaf j) => [(i,j)]
 | fork l r => cherries l ++ cherries r
 | rho u => cherries u

def arm (s : T) (i : Nat) : List T := match s with
 | leaf _ => []
 | fork l r => if contains l i then arm l i ++ [r] else arm r i ++ [l]
 | rho u => arm u i

def lca (s : T) (i j : Nat) : T := match s with
 | leaf _ => s
 | fork l r => if contains l i && contains l j then lca l i j else
      if contains r i && contains r j then lca r i j else s
 | rho u => lca u i j

def pendants (s : T) (i j : Nat) : List T := match s with
 | leaf _ => []
 | fork l r => if contains l i && contains l j then pendants l i j else
      if contains r i && contains r j then pendants r i j else
      if contains l i then arm l i ++ (arm r j).reverse else arm r i ++ (arm l j).reverse
 | rho u => pendants u i j

def cut (s : T) (i : Nat) : Option T := match s with
 | leaf j => if i == j then none else some s
 | fork l r => match cut l i, cut r i with
     | none, none => none
     | some u, none => some u
     | none, some v => some v
     | some u, some v => some (fork u v)
 | rho u => (cut u i).map rho

def chain : List T → Option T
 | [] => none
 | s::ss => some (ss.foldl fork s)

def uncle (f1 : T) (i : Nat) : Option T := (parentSub f1 (leaf i)).bind (siblingSub f1)

def earlier (f1 f2 : T) (prot : List T) (i j : Nat) : List Bool :=
 let ps := pendants f2 i j
 let un := uncle f1 i
 let rb := un.isSome && (siblingSub f2 (leaf i) == un || siblingSub f2 (leaf j) == un)
 let rbs := ps.length >= 2 && parentSub f2 (leaf j) == some (lca f2 i j) && chain ps == un
 let b2 := ps.length == 2 && siblingSub f2 (lca f2 i j) == un && un.isSome
 let bcy := match un, ps.head? with
     | some u, some b => existsSub f2 u && prot.contains u && parentSub f2 u == some b
     | _, _ => false
 [ps.length == 1, rb, rbs, b2, bcy]

def eligible (top : T) (ij : Nat × Nat) : Bool := contains top ij.1 && contains top ij.2

def rankLE (f1 f2 : T) (ij kl : Nat × Nat) : Bool :=
 depth f1 ij.1 < depth f1 kl.1 ||
 (depth f1 ij.1 == depth f1 kl.1 && max (depth f2 ij.1) (depth f2 ij.2) <= max (depth f2 kl.1) (depth f2 kl.2))

def selected (f1 f2 top : T) (ij : Nat × Nat) : Bool :=
 (cherries f1).contains ij && eligible top ij &&
 (cherries f1).all (fun kl => !eligible top kl || rankLE f1 f2 kl ij)

def A0 : T := (rho (fork (fork (fork (fork (fork (fork (leaf 0) (leaf 10)) (leaf 11)) (leaf 1)) (leaf 2)) (fork (fork (leaf 3) (leaf 4)) (leaf 8))) (fork (fork (leaf 5) (leaf 6)) (fork (leaf 7) (leaf 9)))))
def B0 : T := (rho (fork (fork (fork (leaf 0) (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 2) (fork (leaf 4) (leaf 7))))) (fork (leaf 10) (fork (leaf 1) (fork (leaf 11) (leaf 9))))) (leaf 8)))
def P0 : List T := []
def A1 : T := (rho (fork (fork (fork (fork (fork (leaf 0) (leaf 11)) (leaf 1)) (leaf 2)) (fork (fork (leaf 3) (leaf 4)) (leaf 8))) (fork (fork (leaf 5) (leaf 6)) (fork (leaf 7) (leaf 9)))))
def B1 : T := (rho (fork (fork (fork (leaf 0) (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 2) (fork (leaf 4) (leaf 7))))) (fork (leaf 1) (fork (leaf 11) (leaf 9)))) (leaf 8)))
def P1 : List T := [(fork (leaf 1) (fork (leaf 11) (leaf 9))), (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 2) (fork (leaf 4) (leaf 7)))), (leaf 0)]
def A2 : T := (rho (fork (fork (fork (fork (leaf 0) (leaf 1)) (leaf 2)) (fork (fork (leaf 3) (leaf 4)) (leaf 8))) (fork (fork (leaf 5) (leaf 6)) (fork (leaf 7) (leaf 9)))))
def B2 : T := (rho (fork (fork (fork (leaf 0) (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 2) (fork (leaf 4) (leaf 7))))) (fork (leaf 1) (leaf 9))) (leaf 8)))
def P2 : List T := [(fork (leaf 1) (leaf 9)), (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 2) (fork (leaf 4) (leaf 7)))), (leaf 0)]
def A3 : T := (rho (fork (fork (fork (leaf 0) (leaf 2)) (fork (fork (leaf 3) (leaf 4)) (leaf 8))) (fork (fork (leaf 5) (leaf 6)) (fork (leaf 7) (leaf 9)))))
def B3 : T := (rho (fork (fork (fork (leaf 0) (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 2) (fork (leaf 4) (leaf 7))))) (leaf 9)) (leaf 8)))
def P3 : List T := [(leaf 9), (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 2) (fork (leaf 4) (leaf 7)))), (leaf 0)]
def A4 : T := (rho (fork (fork (leaf 0) (fork (fork (leaf 3) (leaf 4)) (leaf 8))) (fork (fork (leaf 5) (leaf 6)) (fork (leaf 7) (leaf 9)))))
def B4 : T := (rho (fork (fork (fork (leaf 0) (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 4) (leaf 7)))) (leaf 9)) (leaf 8)))
def P4 : List T := [(leaf 9), (fork (fork (leaf 5) (fork (leaf 3) (leaf 6))) (fork (leaf 4) (leaf 7))), (fork (leaf 5) (fork (leaf 3) (leaf 6))), (fork (leaf 4) (leaf 7)), (leaf 0)]
def Top1 : T := (fork (leaf 0) (leaf 11))
def Top2 : T := (fork (leaf 0) (leaf 1))
def Top3 : T := (fork (leaf 0) (leaf 2))
def Top4 : T := (fork (leaf 0) (fork (fork (leaf 3) (leaf 4)) (leaf 8)))

def transport (prot : List T) (i : Nat) := prot.filterMap (fun s => cut s i)
def sameProtection (l r : List T) : Bool :=
 l.all (fun x => r.contains x) && r.all (fun x => l.contains x)
def legalCut (f : T) (p cuts : List T) : Bool :=
 cuts.all fun u =>
  existsSub f u && !(p.contains u) && (parentSub f u).isSome &&
  !(parentSub f u == some f && ((siblingSub f u).any fun v => p.contains v))

-- Positive and deliberately violated selection controls precede the witness.
theorem orientation_control : depth B4 3 ≥ depth B4 4 := by decide
theorem wrong_original_eligibility : eligible Top2 (3,4) = false := by decide

theorem cuts :
 cut A0 10 = some A1 ∧ cut B0 10 = some B1 ∧
 cut A1 11 = some A2 ∧ cut B1 11 = some B2 ∧
 cut A2 1 = some A3 ∧ cut B2 1 = some B3 ∧
 cut A3 2 = some A4 ∧ cut B3 2 = some B4 := by decide

theorem selected_pairs :
 selected A0 B0 A0 (0,10) = true ∧
 selected A1 B1 Top1 (0,11) = true ∧
 selected A2 B2 Top2 (0,1) = true ∧
 selected A3 B3 Top3 (0,2) = true ∧
 selected A4 B4 Top4 (3,4) = true := by decide

theorem ordered_pairs :
 depth B0 0 ≥ depth B0 10 ∧ depth B1 11 ≥ depth B1 0 ∧
 depth B2 0 ≥ depth B2 1 ∧ depth B3 2 ≥ depth B3 0 ∧
 depth B4 3 ≥ depth B4 4 := by decide

theorem pendant_counts :
 (pendants B0 0 10).length = 2 ∧ (pendants B1 11 0).length = 3 ∧
 (pendants B2 0 1).length = 2 ∧ (pendants B3 2 0).length = 2 ∧
 (pendants B4 3 4).length = 3 := by decide

theorem no_earlier_rules :
 earlier A0 B0 P0 0 10 = [false,false,false,false,false] ∧
 earlier A1 B1 P1 11 0 = [false,false,false,false,false] ∧
 earlier A2 B2 P2 0 1 = [false,false,false,false,false] ∧
 earlier A3 B3 P3 2 0 = [false,false,false,false,false] ∧
 earlier A4 B4 P4 3 4 = [false,false,false,false,false] := by decide

theorem protection_transport :
 P0 = [] ∧
 sameProtection (transport ([leaf 0] ++ pendants B0 0 10) 10) P1 = true ∧
 sameProtection (transport P1 11) P2 = true ∧
 sameProtection (transport (P2 ++ [leaf 0] ++ pendants B2 0 1) 1) P3 = true ∧
 sameProtection (transport (P3 ++ pendants B3 2 0) 2) P4 = true := by decide

theorem legal_branch_vectors :
 [legalCut B0 P0 [leaf 0], legalCut B0 P0 (pendants B0 0 10), legalCut B0 P0 [leaf 10]] = [true,true,true] ∧
 [legalCut B1 P1 [leaf 11], legalCut B1 P1 (pendants B1 11 0), legalCut B1 P1 [leaf 0]] = [true,false,false] ∧
 [legalCut B2 P2 [leaf 0], legalCut B2 P2 (pendants B2 0 1), legalCut B2 P2 [leaf 1]] = [false,false,true] ∧
 [legalCut B3 P3 (pendants B3 2 0), legalCut B3 P3 [leaf 2]] = [true,true] ∧
 [legalCut B4 P4 [leaf 3], legalCut B4 P4 (pendants B4 3 4), legalCut B4 P4 [leaf 4]] = [true,true,true] := by decide

theorem history_application_failure :
 depth A2 0 = depth A2 3 ∧ depth B2 3 > depth B2 0 ∧
 eligible Top2 (3,4) = false ∧
 ((siblingSub B4 (leaf 0)).any fun b => contains b 3) = true := by decide

-- Source annotation read separately: G1 A2 C adds a; G3 sole child resets;
-- new G1 A2 C adds a; new G3 two-child A2 endpoint branch retains a.
inductive CreditStep where | g1A2C | g3Sole | g3A2Endpoint
def credits : CreditStep → List Nat → List Nat
 | .g1A2C, _ => [0]
 | .g3Sole, _ => []
 | .g3A2Endpoint, p => p
theorem explicit_credit_schedule :
 credits .g1A2C [] = [0] ∧ credits .g3Sole [0] = [] ∧
 credits .g1A2C [] = [0] ∧ credits .g3A2Endpoint [0] = [0] := by decide

#print axioms orientation_control
#print axioms wrong_original_eligibility
#print axioms cuts
#print axioms selected_pairs
#print axioms ordered_pairs
#print axioms pendant_counts
#print axioms no_earlier_rules
#print axioms protection_transport
#print axioms legal_branch_vectors
#print axioms history_application_failure
#print axioms explicit_credit_schedule
end HistoryTrace
