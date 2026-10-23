import GuardedExact
import Lean
open Lean RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller Universal233
namespace IndependentCallerReadout
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def jt : Tree → Json
 | .leaf n => toJson n
 | .node a b => toJson [jt a,jt b]
def jjob (j : Job) : Json := Json.mkObj [("T",jt j.T),("S",jt j.S),("budget",toJson j.budget)]
def jp (T S : Tree) : Json :=
 match hp : DepthOne.pretest01 T S with
 | .refused => Json.mkObj [("status",toJson "REFUSED")]
 | .rejected => Json.mkObj [("status",toJson "REJECT")]
 | .found p => Json.mkObj [("status",toJson (if p.isNone then "FOUND0" else "FOUND1")),("cut",toJson p),("forest",toJson (DepthOne.forest S p))]
def reply (d : Setup) (FX FM : Forest) (T S : Tree) (r : Nat) : Option Forest :=
 let F := if T==d.tx && S==d.sx then FX else FM
 if F.length-1≤r then some F else none
def cb (tag : String) (q : Nat) (d : Setup) (FX FM : Forest) (T S : Tree) (r : Nat) : Option Forest :=
 dbgTrace ("TRACE|"++tag++"|"++toString q++"|"++(if T==d.tx && S==d.sx then "ordinaryX" else if T==d.mxT && S==d.mxS then "markedX" else "UNPAID")++"|"++toString r)
   (fun _ => reply d FX FM T S r)
def row (tag : String) (d : Setup) (q : Nat) (FX FM : Forest) : IO Unit := do
 let result := runGuarded d q (cb tag q d FX FM)
 let FY := match DepthOne.pretest01 d.ty d.sy with | .found c => DepthOne.forest d.sy c | _ => []
 let FN := outsideReply d FY
 let cand := match FN with | none => [] | some F => mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM F
 let hulls := fun T => (FX++FY).map (minimalVertices · T)
 IO.println <| (Json.mkObj [("id",toJson tag),("q",toJson q),("result",toJson result),("status",toJson (match result with | none => "REFUSAL" | some none => "BOUNDED_NEGATIVE" | some (some _) => "MINIMUM")),
   ("callback_replies",toJson ((guardedJobs d q).map (fun j => reply d FX FM j.T j.S j.budget))),("planned_jobs",toJson ((guardedJobs d q).map jjob)),("mass",toJson (toString (guardedMass (233/100) d q))),
   ("trees",toJson [jt d.tx,jt d.sx,jt d.ty,jt d.sy,jt d.mxT,jt d.mxS,jt d.myT,jt d.myS]),
   ("outside",jp d.ty d.sy),("marked_outside",jp d.myT d.myS),("FY",toJson FY),("FN",toJson FN),
   ("FX",toJson FX),("FM",toJson FM),("candidate_multiset",toJson cand),
   ("valid_candidates",toJson (cand.filter (agreement d.T d.S))),
   ("pick",toJson (pickMerge d.T d.S d.X d.Y d.x d.y d.rho d.gamma FM (FN.getD []))),
   ("reconstructed",toJson (reconstruct d FX FY FM (FN.getD []))),
   ("concatenation_valid",toJson (agreement d.T d.S (FX++FY))),
   ("concatenation_hulls_T",toJson (hulls d.T)),("concatenation_hulls_S",toJson (hulls d.S))]).compress
def witness (tag : String) (d : Setup) (F : Forest) : IO Unit :=
 IO.println <| (Json.mkObj [("kind",toJson "WITNESS"),("id",toJson tag),("forest",toJson F),("agreement",toJson (agreement d.T d.S F)),("hulls_T",toJson (F.map (minimalVertices · d.T))),("hulls_S",toJson (F.map (minimalVertices · d.S)))]).compress
def d0 : Setup := {
  T := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  S := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  tx := (.leaf 0)
  sx := (.leaf 0)
  ty := (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  sy := (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2))
  mxT := (.node (.leaf 0) (.leaf 10))
  mxS := (.node (.leaf 0) (.leaf 10))
  myT := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  myS := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  X := [0]
  Y := [1,2,3]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[true],(.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[true],(.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d1 : Setup := {
  T := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  S := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  tx := (.leaf 0)
  sx := (.leaf 0)
  ty := (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  sy := (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  mxT := (.node (.leaf 0) (.leaf 10))
  mxS := (.node (.leaf 0) (.leaf 10))
  myT := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  myS := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  X := [0]
  Y := [1,2,3]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[true],(.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[true],(.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d2 : Setup := {
  T := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))))
  S := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4))))
  tx := (.leaf 0)
  sx := (.leaf 0)
  ty := (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4)))
  sy := (.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4)))
  mxT := (.node (.leaf 0) (.leaf 10))
  mxS := (.node (.leaf 0) (.leaf 10))
  myT := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))))
  myS := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4))))
  X := [0]
  Y := [1,2,3,4]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[true],(.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[true],(.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4))),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d3 : Setup := {
  T := (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4)))))
  S := (.node (.leaf 0) (.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 1) (.leaf 2)))))
  tx := (.leaf 0)
  sx := (.leaf 0)
  ty := (.node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4))))
  sy := (.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 1) (.leaf 2))))
  mxT := (.node (.leaf 0) (.leaf 10))
  mxS := (.node (.leaf 0) (.leaf 10))
  myT := (.node (.leaf 11) (.node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4)))))
  myS := (.node (.leaf 11) (.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 1) (.leaf 2)))))
  X := [0]
  Y := [1,2,3,4]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[true],(.node (.leaf 1) (.node (.leaf 2) (.node (.leaf 3) (.leaf 4)))),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[true],(.node (.leaf 3) (.node (.leaf 4) (.node (.leaf 1) (.leaf 2)))),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d4 : Setup := {
  T := (.node (.node (.leaf 0) (.leaf 4)) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  S := (.node (.node (.leaf 0) (.leaf 4)) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  tx := (.node (.leaf 0) (.leaf 4))
  sx := (.node (.leaf 0) (.leaf 4))
  ty := (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  sy := (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2))
  mxT := (.node (.node (.leaf 0) (.leaf 4)) (.leaf 10))
  mxS := (.node (.node (.leaf 0) (.leaf 4)) (.leaf 10))
  myT := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  myS := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  X := [0,4]
  Y := [1,2,3]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[false],(.node (.leaf 0) (.leaf 4)),by decide,by decide,Or.inr (by decide)⟩
  edgeS := ⟨[true],(.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d5 : Setup := {
  T := (.node (.node (.node (.leaf 0) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))) (.leaf 1)) (.leaf 2))
  S := (.node (.node (.leaf 0) (.node (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4)) (.leaf 1))) (.leaf 2))
  tx := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  sx := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
  ty := (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
  sy := (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4))
  mxT := (.node (.node (.node (.leaf 0) (.leaf 10)) (.leaf 1)) (.leaf 2))
  mxS := (.node (.node (.leaf 0) (.node (.leaf 10) (.leaf 1))) (.leaf 2))
  myT := (.node (.leaf 11) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5)))
  myS := (.node (.leaf 11) (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4)))
  X := [0,1,2]
  Y := [3,4,5]
  x := 0
  y := 3
  rho := 10
  gamma := 11
  edgeT := ⟨[false,false,true],(.node (.node (.leaf 3) (.leaf 4)) (.leaf 5)),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[false,true,false],(.node (.node (.leaf 3) (.leaf 5)) (.leaf 4)),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d6 : Setup := {
  T := (.node (.node (.leaf 0) (.node (.leaf 2) (.node (.leaf 3) (.node (.leaf 4) (.leaf 5))))) (.leaf 1))
  S := (.node (.leaf 0) (.node (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 2) (.leaf 3)))) (.leaf 1)))
  tx := (.node (.leaf 0) (.leaf 1))
  sx := (.node (.leaf 0) (.leaf 1))
  ty := (.node (.leaf 2) (.node (.leaf 3) (.node (.leaf 4) (.leaf 5))))
  sy := (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 2) (.leaf 3))))
  mxT := (.node (.node (.leaf 0) (.leaf 10)) (.leaf 1))
  mxS := (.node (.leaf 0) (.node (.leaf 10) (.leaf 1)))
  myT := (.node (.leaf 11) (.node (.leaf 2) (.node (.leaf 3) (.node (.leaf 4) (.leaf 5)))))
  myS := (.node (.leaf 11) (.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 2) (.leaf 3)))))
  X := [0,1]
  Y := [2,3,4,5]
  x := 0
  y := 2
  rho := 10
  gamma := 11
  edgeT := ⟨[false,true],(.node (.leaf 2) (.node (.leaf 3) (.node (.leaf 4) (.leaf 5)))),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[true,false],(.node (.leaf 4) (.node (.leaf 5) (.node (.leaf 2) (.leaf 3)))),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d7 : Setup := {
  T := (.node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) (.leaf 0))
  S := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  tx := (.leaf 0)
  sx := (.leaf 0)
  ty := (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  sy := (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2))
  mxT := (.node (.leaf 10) (.leaf 0))
  mxS := (.node (.leaf 0) (.leaf 10))
  myT := (.node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) (.leaf 11))
  myS := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  X := [0]
  Y := [1,2,3]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[false],(.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[true],(.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d8 : Setup := {
  T := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  S := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  tx := (.leaf 0)
  sx := (.leaf 0)
  ty := (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  sy := (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2))
  mxT := (.node (.leaf 0) (.leaf 10))
  mxS := (.node (.leaf 0) (.leaf 10))
  myT := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  myS := (.node (.leaf 11) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  X := [0]
  Y := [1,2,3]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[true],(.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[false],(.leaf 0),by decide,by decide,Or.inr (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d9 : Setup := {
  T := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  S := (.node (.leaf 0) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  tx := (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
  sx := (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2))
  ty := (.leaf 0)
  sy := (.leaf 0)
  mxT := (.node (.leaf 10) (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)))
  mxS := (.node (.leaf 10) (.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)))
  myT := (.node (.leaf 0) (.leaf 11))
  myS := (.node (.leaf 0) (.leaf 11))
  X := [1,2,3]
  Y := [0]
  x := 1
  y := 0
  rho := 10
  gamma := 11
  edgeT := ⟨[true],(.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)),by decide,by decide,Or.inr (by decide)⟩
  edgeS := ⟨[true],(.node (.node (.leaf 1) (.leaf 3)) (.leaf 2)),by decide,by decide,Or.inr (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d10 : Setup := {
  T := (.node (.leaf 17) (.node (.node (.leaf 101) (.leaf 5)) (.leaf 999)))
  S := (.node (.leaf 17) (.node (.node (.leaf 101) (.leaf 999)) (.leaf 5)))
  tx := (.leaf 17)
  sx := (.leaf 17)
  ty := (.node (.node (.leaf 101) (.leaf 5)) (.leaf 999))
  sy := (.node (.node (.leaf 101) (.leaf 999)) (.leaf 5))
  mxT := (.node (.leaf 17) (.leaf 10000))
  mxS := (.node (.leaf 17) (.leaf 10000))
  myT := (.node (.leaf 10001) (.node (.node (.leaf 101) (.leaf 5)) (.leaf 999)))
  myS := (.node (.leaf 10001) (.node (.node (.leaf 101) (.leaf 999)) (.leaf 5)))
  X := [17]
  Y := [101,5,999]
  x := 17
  y := 101
  rho := 10000
  gamma := 10001
  edgeT := ⟨[true],(.node (.node (.leaf 101) (.leaf 5)) (.leaf 999)),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[true],(.node (.node (.leaf 101) (.leaf 999)) (.leaf 5)),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def d11 : Setup := {
  T := (.node (.node (.leaf 3) (.node (.leaf 2) (.leaf 1))) (.leaf 0))
  S := (.node (.node (.leaf 2) (.node (.leaf 3) (.leaf 1))) (.leaf 0))
  tx := (.leaf 0)
  sx := (.leaf 0)
  ty := (.node (.leaf 3) (.node (.leaf 2) (.leaf 1)))
  sy := (.node (.leaf 2) (.node (.leaf 3) (.leaf 1)))
  mxT := (.node (.leaf 10) (.leaf 0))
  mxS := (.node (.leaf 10) (.leaf 0))
  myT := (.node (.node (.leaf 3) (.node (.leaf 2) (.leaf 1))) (.leaf 11))
  myS := (.node (.node (.leaf 2) (.node (.leaf 3) (.leaf 1))) (.leaf 11))
  X := [0]
  Y := [1,2,3]
  x := 0
  y := 1
  rho := 10
  gamma := 11
  edgeT := ⟨[false],(.node (.leaf 3) (.node (.leaf 2) (.leaf 1))),by decide,by decide,Or.inl (by decide)⟩
  edgeS := ⟨[false],(.node (.leaf 2) (.node (.leaf 3) (.leaf 1))),by decide,by decide,Or.inl (by decide)⟩
  nt := by decide
  ns := by decide
  hpT := by decide
  hpS := by decide
  htx := by decide
  hsx := by decide
  hty := by decide
  hsy := by decide
  hMXT := by decide
  hMXS := by decide
  hMYT := by decide
  hMYS := by decide
  hx := by decide
  hy := by decide
  frT := by decide
  frS := by decide
  fgT := by decide
  fgS := by decide
}
def main : IO Unit := do
  row "starting-paid" d0 0 [[0]] [[0,10]]
  row "starting-paid" d0 1 [[0]] [[0,10]]
  row "starting-paid" d0 2 [[0]] [[0,10]]
  row "identical-refusal" d1 0 [[0]] [[0,10]]
  row "identical-refusal" d1 1 [[0]] [[0,10]]
  row "identical-refusal" d1 2 [[0]] [[0,10]]
  row "outside-at-least2" d2 0 [[0]] [[0,10]]
  row "outside-at-least2" d2 1 [[0]] [[0,10]]
  row "outside-at-least2" d2 2 [[0]] [[0,10]]
  row "marked-outside-cost2" d3 0 [[0]] [[0,10]]
  row "marked-outside-cost2" d3 1 [[0]] [[0,10]]
  row "marked-outside-cost2" d3 2 [[0]] [[0,10]]
  row "marked-outside-cost2" d3 3 [[0]] [[0,10]]
  row "nonsingleton-X" d4 0 [[0,4]] [[0,4,10]]
  row "nonsingleton-X" d4 1 [[0,4]] [[0,4,10]]
  row "nonsingleton-X" d4 2 [[0,4]] [[0,4,10]]
  row "hard-marked-callback6" d5 0 [[0,1,2]] [[0],[1,2,10]]
  row "hard-marked-callback6" d5 1 [[0,1,2]] [[0],[1,2,10]]
  row "hard-marked-callback6" d5 2 [[0,1,2]] [[0],[1,2,10]]
  row "both-marked-unstable6" d6 0 [[0,1]] [[0],[1,10]]
  row "both-marked-unstable6" d6 1 [[0,1]] [[0],[1,10]]
  row "both-marked-unstable6" d6 2 [[0,1]] [[0],[1,10]]
  row "both-marked-unstable6" d6 3 [[0,1]] [[0],[1,10]]
  row "root-child-swap-T" d7 0 [[0]] [[0,10]]
  row "root-child-swap-T" d7 1 [[0]] [[0,10]]
  row "root-child-swap-T" d7 2 [[0]] [[0,10]]
  row "opposite-cut-sides" d8 0 [[0]] [[0,10]]
  row "opposite-cut-sides" d8 1 [[0]] [[0,10]]
  row "opposite-cut-sides" d8 2 [[0]] [[0,10]]
  row "reverse-roles-refusal" d9 0 [[1],[2,3]] [[1],[2,3,10]]
  row "reverse-roles-refusal" d9 1 [[1],[2,3]] [[1],[2,3,10]]
  row "reverse-roles-refusal" d9 2 [[1],[2,3]] [[1],[2,3,10]]
  row "arbitrary-Nat" d10 0 [[17]] [[17,10000]]
  row "arbitrary-Nat" d10 1 [[17]] [[17,10000]]
  row "arbitrary-Nat" d10 2 [[17]] [[17,10000]]
  row "all-child-swaps" d11 0 [[0]] [[0,10]]
  row "all-child-swaps" d11 1 [[0]] [[0,10]]
  row "all-child-swaps" d11 2 [[0]] [[0,10]]
  witness "starting-paid" d0 [[0,1,2],[3]]
  witness "hard-marked-callback6" d5 [[0,1,2],[3,4],[5]]
  witness "both-marked-unstable6" d6 [[0,1],[2,3],[4,5]]
  witness "root-child-swap-T" d7 [[0,1,2],[3]]
  witness "opposite-cut-sides" d8 [[0,1,2],[3]]
  witness "reverse-roles-refusal" d9 [[0,1,2],[3]]
  witness "arbitrary-Nat" d10 [[17,101,5],[999]]
  witness "all-child-swaps" d11 [[0,1,2],[3]]
end IndependentCallerReadout
def main := IndependentCallerReadout.main
