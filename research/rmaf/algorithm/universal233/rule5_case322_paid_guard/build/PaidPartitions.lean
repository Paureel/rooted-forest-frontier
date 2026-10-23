import CurrentPartition
import PathSpecification
namespace Universal233.Case322PaidGuard
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction
set_option maxRecDepth 20000

theorem filter_sublist_exact {A L : List Nat} (h : A.Sublist L) (hn : L.Nodup) :
 L.filter A.contains = A := by
 induction h with
 | slnil => simp
 | @cons A L a h ih =>
   have nd := List.nodup_cons.1 hn
   have na : a ∉ A := fun ha => nd.1 (h.subset ha)
   simp [na,ih nd.2]
 | @cons_cons A L a h ih =>
   have nd := List.nodup_cons.1 hn
   have eq : L.filter (a::A).contains = L.filter A.contains := by
     apply List.filter_congr
     intro x hx
     have ne : x ≠ a := fun e => nd.1 (e ▸ hx)
     simp [ne]
   simp [eq,ih nd.2]

theorem splitForest_append (P Q : List (List Nat)) (X : List Nat) :
 splitForest (P++Q) X = splitForest P X ++ splitForest Q X := by
 simp [splitForest,BinaryExchange.splitAll,List.flatMap_append]

theorem arcPartitionFrom_append (T : Tree) (qs : List RMAF.Vertex) (P Q : List (List Nat)) :
 arcPartitionFrom T qs (P++Q) = arcPartitionFrom T qs P ++ arcPartitionFrom T qs Q := by
 induction qs generalizing P Q with
 | nil => rfl
 | cons q qs ih => simp only [arcPartitionFrom,splitForest_append,ih]

theorem splitForest_disjoint {A X : List Nat} (ne : A ≠ [])
 (disj : ∀ x, x ∈ A → x ∉ X) : splitForest [A] X = [A] := by
 have yes : BinaryExchange.yes A X.contains = [] := by
   apply List.filter_eq_nil_iff.2
   intro x hx; simpa using disj x hx
 have no : BinaryExchange.no A X.contains = A := by
   apply List.filter_eq_self.2
   intro x hx; simpa using disj x hx
 simp [splitForest,BinaryExchange.splitAll,BinaryExchange.split,yes,no,
   (BinaryExchange.isEmpty_false A).2 ne]

theorem arcPartitionFrom_disjoint {T : Tree} (qs : List RMAF.Vertex) {A : List Nat}
 (ne : A ≠ []) (disj : ∀ q, q ∈ qs → ∀ x, x ∈ A → x ∉ subtreeLabels T q) :
 arcPartitionFrom T qs [A] = [A] := by
 induction qs with
 | nil => rfl
 | cons q qs ih =>
   rw [arcPartitionFrom,splitForest_disjoint ne (disj q (by simp))]
   exact ih (fun r hr => disj r (by simp [hr]))

theorem splitForest_sublist {A L : List Nat} (h : A.Sublist L) (hn : L.Nodup)
 (neA : A ≠ []) (neR : L.filter (fun x => !A.contains x) ≠ []) :
 splitForest [L] A = [A,L.filter (fun x => !A.contains x)] := by
 have yes := filter_sublist_exact h hn
 have no : BinaryExchange.no L A.contains = L.filter (fun x => !A.contains x) := rfl
 have ea := (BinaryExchange.isEmpty_false A).2 neA
 have er := (BinaryExchange.isEmpty_false _).2 neR
 simp only [splitForest,BinaryExchange.splitAll,List.flatMap_cons,List.flatMap_nil,
   List.append_nil,BinaryExchange.split,BinaryExchange.yes,no,yes,
   List.filter_cons,List.filter_nil,ea,er,Bool.not_false,ite_true]

/-- Pairwise disjoint original subtree clusters materialize in the literal cut
order, followed by the original-label residual. Nonemptiness is derived from
an actual retained label, rather than a component-count field. -/
theorem arcPartitionFrom_antichain {T : Tree} (qs : List RMAF.Vertex)
 (L : List Nat) (z : Nat) (hn : L.Nodup)
 (sub : ∀ q, q ∈ qs → (subtreeLabels T q).Sublist L)
 (ne : ∀ q, q ∈ qs → subtreeLabels T q ≠ [])
 (nd : qs.Nodup)
 (disj : ∀ q, q ∈ qs → ∀ r, r ∈ qs → q ≠ r →
   ∀ x, x ∈ subtreeLabels T q → x ∉ subtreeLabels T r)
 (anchor : z ∈ L) (outside : ∀ q, q ∈ qs → z ∉ subtreeLabels T q) :
 arcPartitionFrom T qs [L] = qs.map (subtreeLabels T) ++
   [L.filter (fun x => !((qs.map (subtreeLabels T)).flatten.contains x))] := by
 induction qs generalizing L with
 | nil =>
   have e : L.filter (fun _ => true) = L := List.filter_eq_self.2 (by intros; rfl)
   simp [arcPartitionFrom,e]
 | cons q qs ih =>
   let A := subtreeLabels T q
   let R := L.filter (fun x => !A.contains x)
   have nq : A ≠ [] := ne q (by simp)
   have zR : z ∈ R := by simpa [R,A,anchor] using outside q (by simp)
   have nr : R ≠ [] := by intro e; rw [e] at zR; exact List.not_mem_nil zR
   have nd' := List.nodup_cons.1 nd
   have sub' : ∀ r, r ∈ qs → (subtreeLabels T r).Sublist R := by
     intro r hr
     have eq : (subtreeLabels T r).filter (fun x => !A.contains x) = subtreeLabels T r := by
       apply List.filter_eq_self.2
       intro x hx
       simpa using disj r (by simp [hr]) q (by simp)
         (fun e => nd'.1 (e ▸ hr)) x hx
     rw [←eq]
     exact (sub r (by simp [hr])).filter _
   have aq : arcPartitionFrom T qs [A] = [A] := by
     apply arcPartitionFrom_disjoint qs nq
     intro r hr x hx
     exact disj q (by simp) r (by simp [hr]) (fun e => nd'.1 (e ▸ hr)) x hx
   have tail := ih R (hn.filter _) sub' (fun r hr => ne r (by simp [hr])) nd'.2
     (fun r hr t ht hrt => disj r (by simp [hr]) t (by simp [ht]) hrt)
     zR (fun r hr => outside r (by simp [hr]))
   have rem : R.filter (fun x => !((qs.map (subtreeLabels T)).flatten.contains x)) =
     L.filter (fun x => !(((q::qs).map (subtreeLabels T)).flatten.contains x)) := by
     simp only [R,List.filter_filter,List.map_cons,List.flatten_cons]
     apply List.filter_congr
     intro x hx
     by_cases hA : x ∈ A <;> by_cases hQ : x ∈ (qs.map (subtreeLabels T)).flatten
     all_goals simp [hA,hQ,A] at *
   rw [arcPartitionFrom,splitForest_sublist (sub q (by simp)) hn nq nr]
   change arcPartitionFrom T qs ([A]++[R]) = _
   rw [arcPartitionFrom_append,aq,tail,rem]
   rfl

theorem arcPartition_pendants {T : Tree} {a b z : Nat}
 (hn : (leaves T).Nodup) (qs : List RMAF.Vertex) (nd : qs.Nodup)
 (selected : ∀ q, q ∈ qs → q ∈ cuts T a b)
 (hz : z = a ∨ z = b) (zT : z ∈ leaves T) :
 arcPartition T qs = qs.map (subtreeLabels T) ++
   [(leaves T).filter (fun x => !((qs.map (subtreeLabels T)).flatten.contains x))] := by
 apply arcPartitionFrom_antichain qs (leaves T) z hn
 · intro q hq; exact subtreeLabels_sublist T q
 · intro q hq; exact subtreeLabels_nonempty ((cuts_spec T a b q).1 (selected q hq)).1
 · exact nd
 · intro q hq r hr hqr x hx
   exact pendant_labelsets_disjoint hn (selected q hq) (selected r hr) hqr x hx
 · exact zT
 · intro q hq; exact source_label_outside_pendant (selected q hq) hz zT

theorem pendant_partition_binding {S : Tree} {a b : Nat}
 (hn : (leaves S).Nodup) (ha : a ∈ leaves S) :
 arcPartition S (cuts S a b) = pendantPartition S a b := by
 exact arcPartition_pendants hn _ (pendantOriginal_nodup S a b) (fun _ h => h) (Or.inl rfl) ha

theorem pendant_subset_paid_components {T : Tree} {a b : Nat}
 (hn : (leaves T).Nodup) (ha : a ∈ leaves T)
 (qs : List RMAF.Vertex) (nd : qs.Nodup) (selected : ∀ q, q ∈ qs → q ∈ cuts T a b) :
 (arcPartition T qs).length = qs.length+1 := by
 rw [arcPartition_pendants hn qs nd selected (Or.inl rfl) ha]
 simp

theorem pendant_subset_currentGuard {T S : Tree} {a b : Nat}
 (hn : (leaves T).Nodup) (ha : a ∈ leaves T)
 (qs : List RMAF.Vertex) (nd : qs.Nodup) (selected : ∀ q, q ∈ qs → q ∈ cuts T a b) :
 currentGuard T S (targetBranch T qs) = true := by
 apply target_currentGuard_of_nonredundant hn qs nd
 · intro q hq; exact ((cuts_spec T a b q).1 (selected q hq)).1
 · intro q hq; exact ((cuts_spec T a b q).1 (selected q hq)).2.1
 · exact pendant_subset_paid_components hn ha qs nd selected

theorem hardBranch_currentGuard {T S : Tree} {a b : Nat}
 (hn : (leaves S).Nodup) (ha : a ∈ leaves S) :
 currentGuard T S (hardBranch S a b) = true := by
 have nd : (cuts S a b).Nodup := pendantOriginal_nodup S a b
 have arcs : (cuts S a b).all (fun q => !q.isEmpty && (subtree S q).isSome) = true := by
   apply List.all_eq_true.2
   intro q hq
   obtain ⟨valid,nr,_,_⟩ := (cuts_spec S a b q).1 hq
   obtain ⟨U,hU⟩ := valid
   have ie : q.isEmpty = false := (BinaryExchange.isEmpty_false q).2 nr
   simp [ie,hU]
 have binding := pendant_partition_binding (b:=b) hn ha
 have hp := pendant_partition_check hn ha (b:=b)
 have emb := source_embeddings (a:=a) (b:=b) hn
 have len := partition_length S a b
 simp [currentGuard,hardBranch,current,paid,nd,arcs,hp,emb,len,binding]

theorem singleton_partition_binding {S : Tree} {a b : Nat} {qa : RMAF.Vertex}
 (hn : (leaves S).Nodup) (la : LeafAt S qa a) (hb : b ∈ leaves S) (ne : a ≠ b) :
 arcPartition S [qa] = singletonPartition S a := by
 have labels := source_subtree_labels la
 have sub := subtreeLabels_sublist S qa
 have nr : (leaves S).filter (fun x => !(subtreeLabels S qa).contains x) ≠ [] := by
   have h : b ∈ (leaves S).filter (fun x => !(subtreeLabels S qa).contains x) := by
     simp [labels,leaves,hb,Ne.symm ne]
   intro e; rw [e] at h; exact List.not_mem_nil h
 have split := splitForest_sublist sub hn (by simp [labels,leaves]) nr
 have eq : (leaves S).filter (fun x => !(subtreeLabels S qa).contains x) =
     (leaves S).filter (fun x => x != a) := by
   apply List.filter_congr
   intro x hx
   by_cases h : x = a <;> simp [labels,leaves,h]
 rw [eq] at split
 simpa only [arcPartition,arcPartitionFrom,labels,leaves,singletonPartition] using split

theorem bBranch_currentGuard {T S : Tree} {a b : Nat} {qb : RMAF.Vertex}
 (hn : (leaves S).Nodup) (lb : LeafAt S qb b) (ha : a ∈ leaves S) (ne : b ≠ a) :
 currentGuard T S (bBranch S b qb) = true := by
 have binding := singleton_partition_binding hn lb ha ne
 have hp := singleton_partition_check hn (leafAt_label S qb b lb) ha ne
 have emb := singleton_source_embeddings (a:=b) hn
 have nr := terminal_nonroot lb ha ne
 have ie : qb.isEmpty = false := (BinaryExchange.isEmpty_false qb).2 nr
 have look : subtree S qb = some (.leaf b) := lb
 have len : (singletonPartition S b).length = 2 := rfl
 simp [currentGuard,bBranch,current,paid,hp,emb,ie,look,binding,len]

end Universal233.Case322PaidGuard
