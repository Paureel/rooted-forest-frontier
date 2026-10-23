import Monomial
import PolyPrecontrols
namespace GenericForest.LocalPolynomial.Controls
open RMAF ForestState Universal233 Universal233.CoreProgram Universal233.CoreWork Universal233.WholeSourceWork
set_option maxRecDepth 10000

theorem generation_includes_color : generationBill tree [tree] 0 [] 0>
 (meterGenerate tree (VertexGeometry.colorLabel tree []) 0).measured.work := by decide +kernel

def target4 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : List Tree := [.node (.leaf 0) (.leaf 2),.node (.leaf 1) (.leaf 3)]
def raws := branches target4 crossed ⟨0,1,[]⟩ 1
def mat (io : Nat × Output) := materializationBill target4 crossed 1 io.1 io.2

theorem actual_raws : overlap target4 crossed=some ⟨0,1,[]⟩ ∧ raws.length=2 := by decide

theorem retained_copy_bills : (raws.map mat).sum>mat (raws.headD ⟨0,⟨[],[]⟩⟩) := by decide +kernel

def noneOrd (_ _ : Tree) (_ : Nat) : Option Forest := none

theorem full_local_bill_retained : nonrecursiveBill noneOrd (fun _ _ _=>0) (some target4) crossed 1>
 inspectionBill (some target4) crossed 1 := by decide +kernel

theorem polynomial_boundary : overheadPolynomial 2≤2^50*2^8 ∧ overheadPolynomial 2>4096 := by decide +kernel

theorem exact_empty_local_bill : nonrecursiveBill noneOrd (fun _ _ _=>0) none [] 0=4096 := by decide
end GenericForest.LocalPolynomial.Controls
