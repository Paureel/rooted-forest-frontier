import Std

namespace ThesisTrace
inductive T where
 | leaf : Nat → T
 | fork : T → T → T
 | rho : T → T
 deriving DecidableEq, BEq, Repr
open T
-- a=0,c=1,d=2,x=3,y=4,z=5,w=6,t=7,h=8. rho is a labelled unary root.
def a := leaf 0
def c := leaf 1
def d := leaf 2
def x := leaf 3
def y := leaf 4
def z := leaf 5
def w := leaf 6
def t := leaf 7
def h := leaf 8

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

def U := fork x z
def V := fork (fork y w) t
def B1 := fork U (fork d V)
def B1After := fork U V
def outside := fork (fork z w) (fork t h)
def E := fork x y
def F10 := rho (fork (fork (fork (fork a c) d) E) outside)
def F20 := rho (fork (fork (fork a B1) h) c)
def F11 := rho (fork (fork (fork a d) E) outside)
def F21 := rho (fork (fork a B1) h)
def F12 := rho (fork (fork a E) outside)
def F22 := rho (fork (fork a B1After) h)
def P21 := [a,B1,h]
def P22 := [a,B1After,U,V,h]

-- Structural controls are evaluated by the kernel before the real trace theorem.
theorem cut_control : cut (rho (fork (fork a c) d)) 1 = some (rho (fork a d)) := by decide
theorem null_control : cut F10 100 = some F10 := by decide
theorem restriction_control :
 selected (rho (fork (fork a d) E)) (rho (fork (fork a d) E)) (fork a d) (0,2) = true ∧
 selected (rho (fork (fork a d) E)) (rho (fork (fork a d) E)) (fork a d) (3,4) = false := by decide

-- The source's Step5/6 synchronizes F1 after each selected singleton cut.
theorem cut_trace : cut F10 1 = some F11 ∧ cut F20 1 = some F21 ∧
 cut F11 2 = some F12 ∧ cut F21 2 = some F22 := by decide

theorem depth_trace : selected F10 F20 F10 (0,1) = true ∧
 parentSub F11 a = some (fork a d) ∧ selected F11 F21 (fork a d) (0,2) = true ∧
 parentSub F12 a = some (fork a E) ∧ selected F12 F22 (fork a E) (3,4) = true := by decide

theorem orientation_trace : depth F20 0 > depth F20 1 ∧
 depth F21 2 > depth F21 0 ∧ depth F22 4 > depth F22 3 := by decide

theorem pendant_trace : pendants F20 0 1 = [B1,h] ∧
 pendants F21 2 0 = [V,U] ∧ pendants F22 4 3 = [w,t,z] := by decide

theorem no_earlier_case : earlier F10 F20 [] 0 1 = [false,false,false,false,false] ∧
 earlier F11 F21 P21 2 0 = [false,false,false,false,false] ∧
 earlier F12 F22 P22 4 3 = [false,false,false,false,false] := by decide

theorem selected_cuts_unprotected : !P21.contains d = true ∧
 !P22.contains x = true ∧ !P22.contains y = true ∧
 [w,t,z].all (fun u => !P22.contains u) = true := by decide

#print axioms cut_control
#print axioms null_control
#print axioms restriction_control
#print axioms cut_trace
#print axioms depth_trace
#print axioms orientation_trace
#print axioms pendant_trace
#print axioms no_earlier_case
#print axioms selected_cuts_unprotected
end ThesisTrace

namespace ThesisTrace
open T
-- Protection follows a surviving/subsequently suppressed edge through the cut.
def transport (prot : List T) (i : Nat) := prot.filterMap (fun s => cut s i)
theorem protection_trace : transport [a,B1,h] 1 = P21 ∧
 transport (P21 ++ [V,U]) 2 = [a,B1After,h,V,U] ∧
 [a,B1After,h,V,U].all (fun u => P22.contains u) = true ∧
 P22.all (fun u => [a,B1After,h,V,U].contains u) = true := by decide

-- Every chosen cut is below a non-root binary parent, so the additional
-- component-root sibling-protection exclusion cannot apply in this trace.
theorem no_root_sibling_exclusion :
 parentSub F20 c ≠ some F20 ∧ parentSub F21 d ≠ some F21 ∧
 [x,y,w,t,z].all (fun u => parentSub F22 u != some F22) = true := by decide

-- Follow the C-child of the three-way G4 A3BC: x is cut, y protected.
def F13 := rho (fork (fork a y) outside)
def F23 := rho (fork (fork a (fork z V)) h)
def P23 := [a,fork z V,h,V,z,y]
theorem c_child_dead_end : cut F12 3 = some F13 ∧ cut F22 3 = some F23 ∧
 selected F13 F23 (fork a y) (0,4) = true ∧
 earlier F13 F23 P23 4 0 = [false,false,false,false,false] ∧
 pendants F23 4 0 = [w,t,z] ∧
 P23.contains a = true ∧ P23.contains y = true ∧ P23.contains z = true := by decide

#print axioms protection_trace
#print axioms no_root_sibling_exclusion
#print axioms c_child_dead_end
end ThesisTrace

namespace ThesisTrace.More
open T
-- Separate 13-leaf fixture. Existing names a,c,d,x,y keep their old labels.
def z1 := leaf 5
def z2 := leaf 6
def b2 := leaf 7
def su := leaf 8
def sy := leaf 9
def sv := leaf 10
def u := leaf 11
def v := leaf 12
def E3 := fork (fork x y) (fork u v)
def O3 := fork (fork z1 z2) (fork (fork b2 su) (fork sy sv))
def B3 := fork z1 (fork d z2)
def B3a := fork z1 z2
def R0 := fork (fork (fork a B3) b2) c
def R1 := fork (fork a B3) b2
def R2 := fork (fork a B3a) b2

def A0 := rho (fork (fork (fork (fork a c) d) E3) O3)
def A1 := rho (fork (fork (fork a d) E3) O3)
def A2 := rho (fork (fork a E3) O3)
def A3 := rho (fork (fork a (fork x (fork u v))) O3)
def A4 := rho (fork (fork a (fork x u)) O3)
def B0 := rho (fork (fork (fork x R0) (fork u su)) (fork (fork y sy) (fork v sv)))
def B1t := rho (fork (fork (fork x R1) (fork u su)) (fork (fork y sy) (fork v sv)))
def B2t := rho (fork (fork (fork x R2) (fork u su)) (fork (fork y sy) (fork v sv)))
def B3t := rho (fork (fork (fork x R2) (fork u su)) (fork sy (fork v sv)))
def B4t := rho (fork (fork (fork x R2) (fork u su)) (fork sy sv))
def Pr1 := [a,B3,b2]
def Pr2 := [a,B3a,b2,z2,z1]
def Pr3 := Pr2 ++ [x]
def Pr4 := Pr3 ++ [u]

theorem cuts : cut A0 1 = some A1 ∧ cut B0 1 = some B1t ∧
 cut A1 2 = some A2 ∧ cut B1t 2 = some B2t ∧
 cut A2 4 = some A3 ∧ cut B2t 4 = some B3t ∧
 cut A3 12 = some A4 ∧ cut B3t 12 = some B4t := by decide

theorem selected_pairs : selected A0 B0 A0 (0,1) = true ∧
 selected A1 B1t (fork a d) (0,2) = true ∧
 selected A2 B2t (fork a E3) (3,4) = true ∧
 selected A3 B3t (fork x (fork u v)) (11,12) = true ∧
 selected A4 B4t (fork x u) (3,11) = true := by decide

theorem top_and_orientation : parentSub A1 a = some (fork a d) ∧
 parentSub A2 a = some (fork a E3) ∧
 parentSub A3 x = some (fork x (fork u v)) ∧
 parentSub A4 x = some (fork x u) ∧ parentSub A4 u = some (fork x u) ∧
 depth B0 0 > depth B0 1 ∧ depth B1t 2 > depth B1t 0 ∧
 depth B2t 3 ≥ depth B2t 4 ∧ depth B3t 11 ≥ depth B3t 12 := by decide

theorem counts_and_earlier : (pendants B0 0 1).length = 2 ∧
 (pendants B1t 2 0).length = 2 ∧ (pendants B2t 3 4).length = 4 ∧
 (pendants B3t 11 12).length = 4 ∧ (pendants B4t 3 11).length = 2 ∧
 earlier A0 B0 [] 0 1 = [false,false,false,false,false] ∧
 earlier A1 B1t Pr1 2 0 = [false,false,false,false,false] ∧
 earlier A2 B2t Pr2 3 4 = [false,false,false,false,false] ∧
 earlier A3 B3t Pr3 11 12 = [false,false,false,false,false] := by decide

theorem protection_and_legality :
 transport [a,B3,b2] 1 = Pr1 ∧ transport (Pr1 ++ [z2,z1]) 2 = Pr2 ∧
 transport (Pr2 ++ [x]) 4 = Pr3 ∧ transport (Pr3 ++ [u]) 12 = Pr4 ∧
 !Pr1.contains d = true ∧
 [x,y].all (fun s => !Pr2.contains s) = true ∧
 (pendants B2t 3 4).all (fun s => !Pr2.contains s) = true ∧
 [u,v].all (fun s => !Pr3.contains s) = true ∧
 (pendants B3t 11 12).all (fun s => !Pr3.contains s) = true := by decide

theorem credit_cardinality : ([a,x,u].eraseDups).length = 3 ∧
 ([x,u].eraseDups).length = 2 := by decide

#print axioms cuts
#print axioms selected_pairs
#print axioms top_and_orientation
#print axioms counts_and_earlier
#print axioms protection_and_legality
#print axioms credit_cardinality
end ThesisTrace.More
