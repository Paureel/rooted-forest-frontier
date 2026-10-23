import GroupedPrepareBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF ForestState ForestGroups Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.GroupedFullQuery Universal233.PaidQueries Universal233.Rule5SelectedLocalWork

def groupProblemPolynomial (N : Nat):=16*(N+1)^2+64*(N+1)^3+12

theorem groupProblemMeter_bound (T : Tree) (ss : List Tree) (U : List Nat) (N : Nat)
 (tn:treeNodes T≤N) (nodes:∀s,s∈ss→treeNodes s≤N) (sl:ss.length≤N) (ul:U.length≤2*N) :
 (groupProblemMeter (some T) ss U).work≤groupProblemPolynomial N:=by
 have t:=localTargetMeter_bound T U N tn ul
 have s:=ownedMeter_bound ss U N nodes sl ul
 simp only [groupProblemMeter,groupProblemPolynomial];omega

def groupPretestSize (N : Nat):=N*N+N+1

theorem groupProblem_source_forest_caps (T S : Tree) (P : List (List Nat)) (U : List Nat) (N : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (pl:P.length≤N) :
 targetNodes (groupProblem (some T) (OutputState.sourceForest S P) U).target≤groupPretestSize N ∧
 sourceNodes (groupProblem (some T) (OutputState.sourceForest S P) U).sources≤groupPretestSize N ∧
 (groupProblem (some T) (OutputState.sourceForest S P) U).sources.length≤groupPretestSize N:=by
 have t:=localTarget_nodes_cap T U N tn
 have c:=owned_source_forest_caps S P U N sn
 have ns:=sourceNodes_list_cap _ N c.2
 have mul:=Nat.mul_le_mul_right N (Nat.le_trans c.1 pl)
 simp only [groupProblem,groupPretestSize]
 exact ⟨by omega,by omega,by omega⟩

def groupJobsForPolynomial (N : Nat):=
 (4*(N+2)*N+8)*(N+1)+2*N+4+3*(groupProblemPolynomial N+4)+
 2*(groupPrepareOnePolynomial (groupPretestSize N)+8)+18

theorem groupJobsForMeter_bound (T S : Tree) (A B C : List Nat) (o : CoreProgram.Output) (N : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N)
 (pl:o.partition.length≤N) (blocks:∀U,U∈o.partition→U.length≤N) :
 (groupJobsForMeter T S A B C o).work≤groupJobsForPolynomial N:=by
 let ss:=(sourceForestMeter S o.partition).value
 have sl:ss.length≤N:=Nat.le_trans (source_forest_count S o.partition) pl
 have nodes:∀s,s∈ss→treeNodes s≤N:=by intro s hm;exact Nat.le_trans (source_forest_payload S o.partition hm).1 sn
 have material:=source_forest_work S o.partition N blocks
 have sourcecap:(sourceForestMeter S o.partition).work≤(4*(N+2)*N+8)*(N+1):=by
  have first:(4*(N+2)*treeNodes S+3)*o.partition.length+1≤
    (4*(N+2)*treeNodes S+4)*(o.partition.length+1):=by
   simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one];omega
  have mono:=Nat.mul_le_mul
    (show 4*(N+2)*treeNodes S+4≤4*(N+2)*N+8 by
      have m:=Nat.mul_le_mul_left (4*(N+2)) sn;omega)
    (Nat.add_le_add_right pl 1)
  exact Nat.le_trans material (Nat.le_trans first mono)
 have glen:((appendLabelsMeter A B).value).length≤2*N:=by simp only [appendLabelsMeter_value,List.length_append];omega
 have point:∀U,U∈[(appendLabelsMeter A B).value,C]→(groupProblemMeter (some T) ss U).work≤groupProblemPolynomial N:=by
  intro U hm
  have ul:U.length≤2*N:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at hm;rcases hm with rfl|rfl <;> omega
  exact groupProblemMeter_bound T ss U N tn nodes sl ul
 have groups:=meterMap_bound (groupProblemMeter (some T) ss) _ (groupProblemPolynomial N) point
 have caps:∀p,p∈(groupProblemsMeter (some T) ss [(appendLabelsMeter A B).value,C]).value→
  targetNodes p.target≤groupPretestSize N ∧ sourceNodes p.sources≤groupPretestSize N ∧ p.sources.length≤groupPretestSize N:=by
  intro p hm
  simp only [groupProblemsMeter_value,groupProblems,List.mem_map] at hm
  obtain ⟨U,hu,eq⟩:=hm
  subst p
  have c:=groupProblem_source_forest_caps T S o.partition U N tn sn pl
  simpa only [ss,source_forest_value,OutputState.sourceForest] using c
 have jobs:=groupPrepareMeter_bound _ (groupPretestSize N) caps
 have jl:(groupProblemsMeter (some T) ss [(appendLabelsMeter A B).value,C]).value.length=2:=by
  simp only [groupProblemsMeter_value,groupProblems,List.length_map,List.length_cons,List.length_nil]
 rw [jl] at jobs
 simp only [List.length_cons,List.length_nil] at groups
 simp only [groupJobsForMeter,appendLabelsMeter,groupJobsForPolynomial,groupProblemsMeter]
 change _≤_
 dsimp only [ss] at groups jobs
 simp only [appendLabelsMeter_value,groupProblemsMeter] at groups jobs
 omega
end OrdinaryDispatch.Hard2SourceWork
