import PairGuards
import OrdinaryLocal
import MassAssembly
namespace Universal233.Hard2PaidLocal
open RMAF CoreProgram SourceCoverage VertexGeometry BothBad Integration

inductive Kind where
 | clique : RMAF.Vertex → Kind
 | four : RMAF.Vertex → RMAF.Vertex → Kind
 | diagonal : RMAF.Vertex → RMAF.Vertex → Kind
 | vertex : RMAF.Vertex → Kind
 | side : List Nat → Kind
 deriving DecidableEq,Repr
def outputs (kind : Kind) (S T : Tree) (A B : List Nat) (q : Nat) : List Output :=
 match kind with
 | .clique v => WholeSourceMass.cliqueOutputs S T A B v q
 | .four v w => WholeSourceMass.fourChainOutputs S T A B v w q
 | .diagonal v w => WholeSourceMass.diagonalOutputs S T A B v w q
 | .vertex v => PairAssembly.vertexPairOutputs S T A B v q
 | .side D => PairAssembly.sideOutputs S A B D q

/-- Exact full-source payment, materialization, checks, least answer and calls. -/
def runOutputs (actual : BothBadLocal.Ordinary) (T S : Tree) (q : Nat) (outs : List Output) : Execution :=
 execute (GenericForest.solve actual) T S q (entries q .full outs)

theorem outputs_generated (kind : Kind) (S T : Tree) (A B : List Nat) (q : Nat) (o : Output)
 (mem : o∈outputs kind S T A B q) :
 ∃ca cb cc : Nat → Nat,o∈WholeSourceMass.wholeOutputs S A B ca cb cc q := by
 cases kind with
 | clique v =>
  simp only [outputs,WholeSourceMass.cliqueOutputs,List.mem_append] at mem
  rcases mem with (h|h)|h <;> exact ⟨_,_,_,h⟩
 | four v w =>
  simp only [outputs,WholeSourceMass.fourChainOutputs,List.mem_append] at mem
  rcases mem with ((h|h)|h)|h <;> exact ⟨_,_,_,h⟩
 | diagonal v w =>
  simp only [outputs,WholeSourceMass.diagonalOutputs,List.mem_append] at mem
  rcases mem with h|h <;> exact ⟨_,_,_,h⟩
 | vertex v =>
  simp only [outputs,PairAssembly.vertexPairOutputs,List.mem_append] at mem
  rcases mem with h|h <;> exact ⟨_,_,_,h⟩
 | side D => exact ⟨_,_,_,mem⟩

theorem localColors_positive (D : List Nat) (f : Nat → Nat) (ne : D≠[]) :
 1≤(WholeSourceMass.localColors D f).length := by
 obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil D ne
 have mem := (WholeSourceMass.mem_localColors D f (f x)).2 ⟨x,hx,rfl⟩
 have pos := List.length_pos_iff.2 (List.ne_nil_of_mem mem)
 omega

/-- All output facts are derived from the actual tagged source generators. -/
theorem generated_output_facts {S T : Tree} {A B C : List Nat} {q : Nat} {o : Output} (kind : Kind)
 (hs : (leaves S).Nodup) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (mem : o∈outputs kind S T A B q) :
 partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
 CutRealization.RealizedOutput S o ∧ o.partition.length=o.sourceCuts.length+1 ∧
 2≤o.sourceCuts.length ∧ o.sourceCuts.length≤q := by
 obtain ⟨ca,cb,cc,ho⟩ := outputs_generated kind S T A B q o mem
 have valid := Assembly.generated_source_valid S (WholeSourceMass.taggedColor A B ca cb cc) q o ho
 have real := CutRealization.generate_original_realization S (WholeSourceMass.taggedColor A B ca cb cc) q o ho
 have shape := RankDichotomy.generate_partition_cost S (WholeSourceMass.taggedColor A B ca cb cc) q o ho
 have budget := generate_output_budget S (WholeSourceMass.taggedColor A B ca cb cc) q o ho
 have call := PaidAssembly.partition_mass_interface S S A B C hp hs (fun _ h=>h)
 have count := generate_color_cost S (WholeSourceMass.taggedColor A B ca cb cc) q o ho
 change (dedupNat ((leaves S).map (WholeSourceMass.taggedColor A B ca cb cc))).length≤o.sourceCuts.length+1 at count
 rw [WholeSourceMass.taggedColor_cardinality S A B C call.partition] at count
 have a:=localColors_positive A ca call.aNonempty
 have b:=localColors_positive B cb call.bNonempty
 have c:=localColors_positive C cc call.cNonempty
 exact ⟨valid.1,valid.2,real,shape,by omega,budget⟩
end Universal233.Hard2PaidLocal
