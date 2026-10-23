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
def ds : Setup := {
 T := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5)))
 S := (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4)))
 tx := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
 sx := (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1))
 ty := (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
 sy := (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4))
 mxT := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 10))
 mxS := (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) (.leaf 10))
 myT := (.node (.leaf 11) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5)))
 myS := (.node (.leaf 11) (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4)))
 X := [0,1,2]
 Y := [3,4,5]
 x := 0
 y := 3
 rho := 10
 gamma := 11
 edgeT := ⟨[true],(.node (.node (.leaf 3) (.leaf 4)) (.leaf 5)),by decide,by decide,Or.inl (by decide)⟩
 edgeS := ⟨[true],(.node (.node (.leaf 3) (.leaf 5)) (.leaf 4)),by decide,by decide,Or.inl (by decide)⟩
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
 row "ordinary-and-marked-failure6-postcontact" ds 0 [[0,2],[1]] [[0,2,10],[1]]
 row "ordinary-and-marked-failure6-postcontact" ds 1 [[0,2],[1]] [[0,2,10],[1]]
 row "ordinary-and-marked-failure6-postcontact" ds 2 [[0,2],[1]] [[0,2,10],[1]]
 row "ordinary-and-marked-failure6-postcontact" ds 3 [[0,2],[1]] [[0,2,10],[1]]
 witness "ordinary-and-marked-failure6-postcontact" ds [[0,2,3,5],[1],[4]]
 IO.println <| (Json.mkObj [("kind",toJson "DUPLICATE_RAW"),("candidates",toJson (mergeCandidates [0] [1,2,3] 0 1 10 11 [[0,10],[0,10]] [[1],[11,3,2]]))]).compress
end IndependentCallerReadout
def main := IndependentCallerReadout.main
