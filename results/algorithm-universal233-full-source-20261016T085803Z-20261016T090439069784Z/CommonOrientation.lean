import EarlyFacts
namespace OrdinaryDispatch.FastOrdinary
open RMAF ForestState Universal233 Universal233.CherryBranching

def commonPair (T S : Tree) (reverse : Bool) (c : Candidate) : Tree×Tree :=
 let p := Oriented reverse T S
 let z := commonFresh p.1
 (contract c.a c.b z p.1,contract c.a c.b z p.2)

def expandCommon (T S : Tree) (reverse : Bool) (c : Candidate) (F : CommonForest) : CommonForest :=
 F.map (expandBlock c.a c.b (commonFresh (Oriented reverse T S).1))

theorem oriented_proper {T S : Tree} (hp : DepthOne.proper T S=true) (reverse : Bool) :
 DepthOne.proper (Oriented reverse T S).1 (Oriented reverse T S).2=true := by
 cases reverse
 · exact hp
 · exact proper_reverse hp

theorem common_pair_label_count {T S : Tree} {c : Candidate} {reverse : Bool}
 (hp : DepthOne.proper T S=true)
 (sel : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c)) :
 (leaves (commonPair T S reverse c).1).length+1=(leaves T).length := by
 have dec := selected_common_label_decrease (ordinary_state_proper (oriented_proper hp reverse)) sel
 cases reverse
 · exact dec
 · have perm := ((DepthOne.proper_iff T S).1 hp).2.2
   have len := perm.length_eq
   change (leaves (contract c.a c.b (commonFresh S) S)).length+1=(leaves T).length
   simp only [Oriented,ite_true] at dec
   omega

theorem common_pair_fresh (T S : Tree) (reverse : Bool) :
 commonFresh (Oriented reverse T S).1∉leaves (Oriented reverse T S).1 :=
 commonFresh_not_mem _

theorem common_pair_ready {T S : Tree} {c : Candidate} {reverse : Bool}
 (hp : DepthOne.proper T S=true)
 (sel : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c)) :
 DepthOne.proper (commonPair T S reverse c).1 (commonPair T S reverse c).2=true ∧
 (leaves (commonPair T S reverse c).1).length<(leaves T).length := by
 have op := oriented_proper hp reverse
 have state := ordinary_state_proper op
 have ready := selected_common_ready state sel
 have reduced := common_reduced_proper ready
 have prop := GenericForest.singleton_ordinary_proper _ _ reduced
 refine ⟨prop,?_⟩
 cases reverse
 · have dec := selected_common_label_decrease state sel
   simp only [Oriented,Bool.false_eq_true,ite_false] at dec
   change (leaves (contract c.a c.b (commonFresh T) T)).length<(leaves T).length
   omega
 · exact common_reverse_label_decrease hp sel

theorem oriented_query_reverse {T S : Tree} {q : Nat} {reverse : Bool} {answer : Option CommonForest}
 (ex : QueryExact (Oriented reverse T S).1 (Oriented reverse T S).2 q answer) : QueryExact T S q answer := by
 cases reverse
 · exact ex
 · exact query_reverse ex

theorem common_pair_exact {T S : Tree} {c : Candidate} {reverse : Bool}
 (hp : DepthOne.proper T S=true)
 (sel : select (Oriented reverse T S).1 (Oriented reverse T S).2=some (.common,c))
 (q : Nat) (answer : Option CommonForest)
 (ex : QueryExact (commonPair T S reverse c).1 (commonPair T S reverse c).2 q answer) :
 QueryExact T S q (answer.map (expandCommon T S reverse c)) := by
 let p := Oriented reverse T S
 let callback : Tree→Tree→Nat→Option CommonForest := fun _ _ _ => answer
 have consumed := selected_common_query_exact callback q
   (ordinary_state_proper (oriented_proper hp reverse)) sel ex
 apply oriented_query_reverse (reverse:=reverse)
 exact consumed
end OrdinaryDispatch.FastOrdinary
