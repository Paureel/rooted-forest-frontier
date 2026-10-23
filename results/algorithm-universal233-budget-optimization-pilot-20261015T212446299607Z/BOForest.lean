import FastExact
import FinalWork
import MarkerSingleton

namespace OrdinaryDispatch.BudgetOptimization
open RMAF Universal233 OrdinaryCommonSplit RestrictionBridge VertexGeometry

/-- Proof witness only: this forest is never constructed by the optimizer. -/
def singletons (L : List Nat) : CommonForest := L.map (fun x => [x])

theorem singletons_partition (L : List Nat) (hn : L.Nodup) :
 partitionCheck L (singletons L)=true := by
 induction L with
 | nil => rfl
 | cons x L ih =>
   exact partition_add_singleton L x (singletons L) (List.nodup_cons.1 hn).1
     (ih (List.nodup_cons.1 hn).2)

theorem singletons_embeddings (T : Tree) (L : List Nat) (ht : (leaves T).Nodup)
 (hn : L.Nodup) : pairwiseEmbeddings T (singletons L)=true := by
 induction L with
 | nil => rfl
 | cons x L ih =>
   change (singletons L).all (fun b => disjointVertices (minimalVertices [x] T)
     (minimalVertices b T)) && pairwiseEmbeddings T (singletons L)=true
   rw [Bool.and_eq_true]
   refine ⟨List.all_eq_true.2 ?_,ih (List.nodup_cons.1 hn).2⟩
   intro b hb
   obtain ⟨y,hy,rfl⟩ := List.mem_map.1 hb
   apply (clear_iff _ _).2
   apply OrdinaryCommonSplit.singleton_clear T x [y] ht
   have ne : x≠y := by intro h;subst y;exact (List.nodup_cons.1 hn).1 hy
   simpa using ne

theorem singletons_agreement (T S : Tree) (hp : DepthOne.proper T S=true) :
 agreement T S (singletons (leaves T))=true := by
 have h := (DepthOne.proper_iff T S).1 hp
 have perm : (leaves T).Perm (leaves S) := by
   simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] using hp |>.2
 have pt := singletons_partition (leaves T) h.1
 have ps : partitionCheck (leaves S) (singletons (leaves T))=true :=
   (partition_labels_congr (leaves S) (leaves T) _ (fun _ => perm.symm.mem_iff)).2 pt
 simp only [agreement,Bool.and_eq_true]
 refine ⟨⟨⟨⟨pt,ps⟩,?_⟩,singletons_embeddings T _ h.1 h.1⟩,
   singletons_embeddings S _ h.2.1 h.1⟩
 apply List.all_eq_true.2
 intro b hb
 obtain ⟨x,hx,rfl⟩ := List.mem_map.1 hb
 simp [restrictionAgrees,restrict_singleton T x h.1 hx,
   restrict_singleton S x h.2.1 (perm.mem_iff.1 hx),sameShape]

end OrdinaryDispatch.BudgetOptimization
