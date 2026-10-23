import EarlyFacts
namespace OrdinaryDispatch.FastOrdinary
open RMAF ForestState Universal233 Universal233.CherryBranching

def cutoff (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat) : Tree→Tree→Nat→Option CommonForest :=
 fun T S r => if r<q then rec r T S else none

theorem cutoff_refuses (rec : Nat→Tree→Tree→Option CommonForest) (q r : Nat)
 (hr : q≤r) (T S : Tree) : cutoff rec q T S r=none := by simp [cutoff,show ¬r<q by omega]

theorem cutoff_local (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat)
 (ih : ∀b,b<q →∀T S,DepthOne.proper T S=true →QueryExact T S b (rec b T S))
 (r : Nat) (hr : r<q) : ForestMinCompletion.LocalOrdinaryIH r (cutoff rec q) := by
 constructor
 · intro T S b F hb proper answer
   have bq : b<q := by omega
   have returned : rec b T S=some F := by simpa [cutoff,bq] using answer
   exact query_sound (ih b bq T S proper) returned
 · intro T S b F hb proper af budget
   have bq : b<q := by omega
   obtain ⟨G,hG⟩ := query_complete (ih b bq T S proper) F af budget
   exact ⟨G,by simpa [cutoff,bq] using hG⟩

theorem paid_callback_lex (q r n : Nat) (u : Tree) (hr : r<q) :
 Prod.Lex (fun a b : Nat => a<b) (fun a b : Nat => a<b) (r,(leaves u).length) (q,n) :=
 Prod.Lex.left _ _ hr

theorem common_callback_lex (q n : Nat) (u : Tree) (hn : (leaves u).length<n) :
 Prod.Lex (fun a b : Nat => a<b) (fun a b : Nat => a<b) (q,(leaves u).length) (q,n) :=
 Prod.Lex.right _ hn
end OrdinaryDispatch.FastOrdinary
