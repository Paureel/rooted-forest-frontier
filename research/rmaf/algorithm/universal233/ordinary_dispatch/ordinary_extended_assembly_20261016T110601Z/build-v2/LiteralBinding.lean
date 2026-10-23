import LiteralBounds
set_option maxHeartbeats 800000
namespace Universal233.PaidLiteralDecisionWork
open RMAF CoreGraph HardParent CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork Rule5RemainingLocalWork
open Rule5PaidSelector Rule5Classification Rule5FinalClassification Case322PaidGuard Case322Extraction

theorem bottom_nodes (sa sc sb : Bool) (a b c : Nat) (X : Tree) :
 treeNodes (bottom sa sc sb a b c X)=treeNodes X+6 := by
 cases sa <;> cases sc <;> cases sb <;> simp [bottom,VC,AX,orient,treeNodes] <;> omega

/-- Uniform polynomial on payloads, independent of guard success or failure. -/
theorem literal_work (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) (N : Nat)
 (ht : (leaves T).length≤N) (hs : (leaves S).length≤N)
 (hx : (leaves R.X).length≤N) (hc : (leaves C).length≤N)
 (hw : R.w.length≤N) (hqa : qa.length≤N) (hub : ub.length≤N)
 (hu : u.length≤N) (hv : v.length≤N) (hb : d.badArc.length≤N) :
 (literalMeter T S a b d u v R C qa ub).work≤literalBudget N := by
 have p:=proper_pair_work T S N ht hs
 have s:=at_tree_work S R.w (bottom R.sa R.sc R.sb R.a R.b d.c R.X)
 rw [bottom_nodes] at s
 have nx:=treeNodes_le_twice_leaves R.X
 have sb : (bump 10 (atTreeMeter S R.w (bottom R.sa R.sc R.sb R.a R.b d.c R.X))).work≤8*N+31 := by
  simp only [bump_work];omega
 have ch:=cherry_exists_work T R.a R.b
 have chm:=cherry_budget_mono (leaves T).length N ht
 have cut:=cuts_work S R.a R.b
 have cutn:=cuts_count S R.a R.b
 have cutm:=cuts_budget_mono (leaves S).length N hs
 have cb : (cutsTwoMeter S R.a R.b).work≤cutsBudget N+2*N+3 := by
  simp only [cutsTwoMeter];omega
 have ls:=labels_work T C R.X d.c
 have lm:=labels_budget_mono (leaves T).length (leaves C).length (leaves R.X).length N ht hc hx
 have mb:=membership_work C R.b N hc
 have mc:=membership_work C d.c N hc
 have la:=leaf_at_work T qa R.a
 have lb:=leaf_at_work T ub R.b
 have lc:=leaf_at_work T u d.c
 have i1:=incident_eq_work T R.X u v N ht hx hu hv
 have i2:=incident_eq_work T R.X v u N ht hx hv hu
 have ib:=or_work (incidentEqMeter T R.X u v) (fun _=>incidentEqMeter T R.X v u)
 have tv:=tail_mem_work T R.X v N ht hx hv
 have tu:=tail_mem_work T R.X u N ht hx hu
 have mv:=minimal_mem_work T R.X v N ht hx hv
 have mu:=minimal_mem_work T R.X u N ht hx hu
 have bd:=boundary_eq_work S R.X d.badArc N hs hx hb
 have bill:=checks_work (literalChecks T S a b d u v R C qa ub)
 simp only [literalChecks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,
  List.length_nil,Nat.reduceAdd,notMeter] at bill
 change (literalMeter T S a b d u v R C qa ub).work≤_ at bill
 unfold literalBudget
 omega

/-- The precise paid LiteralCall domain is retained, including rejected guards. -/
theorem literal_call_work (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (j : LiteralCall) (dom : LiteralCallDomain T S a b d u v j)
 (hu : u.length≤(leaves T).length) (hv : v.length≤(leaves T).length)
 (hb : d.badArc.length+1≤(leaves S).length) :
 literalFee T S a b j≤literalBudget ((leaves T).length+(leaves S).length) := by
 have p:=literal_call_payload T S a b d u v dom
 rcases dom with ⟨hr,hcore,hqa,hub,hd,hju,hjv⟩
 unfold literalFee
 rw [hd,hju,hjv]
 apply literal_work
 all_goals omega

/-- The arbitrary LiteralCall fee is replaced by the implemented source fee. -/
theorem paid_selected_work_concrete (classFee : CheckRequest→Nat) (T S : Tree) (a b L Kc : Nat)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L)
 (classifier : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r→classFee r≤Kc) :
 (paidSelectedMeter classFee (literalFee T S a b) T S a b).work≤
 paidSelectedBudget (leaves T).length (leaves S).length Kc
  (literalBudget ((leaves T).length+(leaves S).length)) := by
 apply paid_selected_work classFee (literalFee T S a b) T S a b L Kc
  (literalBudget ((leaves T).length+(leaves S).length)) tlabs slabs classifier
 intro d u v sel j dom
 have p:=final_payload classFee T S a b sel
 exact literal_call_work T S a b d u v j dom p.2.2.2.1 p.2.2.2.2 p.1

end Universal233.PaidLiteralDecisionWork
