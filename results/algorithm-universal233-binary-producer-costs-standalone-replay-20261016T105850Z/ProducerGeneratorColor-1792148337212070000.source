import ProducerOverlap
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork
abbrev Color:=Bool×Bool
/-- Proof-only mathematical color projection; the executable representation
contains exactly two Boolean cells. -/
def colorValue (c : Color) : Nat:=if c.2 then (if c.1 then 3 else 2) else (if c.1 then 1 else 0)
def colorEq (a b : Color) : Charged Bool:=⟨(a.1==b.1)&&(a.2==b.2),8⟩
@[simp] theorem colorEq_value (a b : Color) : (colorEq a b).value=(colorValue a==colorValue b) := by
 rcases a with ⟨aa,ab⟩;rcases b with ⟨ba,bb⟩;cases aa <;> cases ab <;> cases ba <;> cases bb <;> decide

def regionBits : RMAF.Vertex→RMAF.Vertex→Charged Color
 | [],[]=>⟨(true,true),4⟩
 | [],false::_=>⟨(false,false),4⟩
 | [],true::_=>⟨(true,false),4⟩
 | _::_,[]=>⟨(false,true),4⟩
 | s::v,t::a=>if s==t then let r:=regionBits v a;⟨r.value,r.work+4⟩ else ⟨(false,true),4⟩
@[simp] theorem regionBits_value (v a : RMAF.Vertex) : colorValue (regionBits v a).value=VertexGeometry.region v a := by
 induction v generalizing a with
 | nil=>cases a with
   | nil=>rfl
   | cons b bs=>cases b <;> rfl
 | cons s v ih=>
  simp only [colorValue] at ih
  cases a with
  | nil=>rfl
  | cons t a=>by_cases h : s=t <;> simp [regionBits,VertexGeometry.region,h,ih,colorValue]

def leafListBits (B : Block) : BinaryProvider.Tree→Charged Addresses
 | .leaf x=>let c:=containsLabel x B;⟨if c.value then [[]] else [],c.work+8⟩
 | .node l r=>let a:=leafListBits B l;let b:=leafListBits B r
               let al:=prependAddresses false a.value;let bl:=prependAddresses true b.value
               let c:=appendSpine al.value bl.value
               ⟨c.value,a.work+b.work+al.work+bl.work+c.work+8⟩
@[simp] theorem leafListBits_value (B : Block) (T : BinaryProvider.Tree) :
 (leafListBits B T).value=VertexGeometry.leafList (blockValue B) (treeValue T) := by
 induction T with
 | leaf x=>simp [leafListBits,BinaryProducer.containsLabel_value,VertexGeometry.leafList,treeValue,labelValue]
 | node l r ihl ihr=>simp [leafListBits,treeValue,VertexGeometry.leafList,RMAF.prependSide,ihl,ihr]

def colorBits (T : BinaryProvider.Tree) (v : RMAF.Vertex) (x : Bits) : Charged Color:=
 let a:=leafListBits [x] T;let r:=regionBits v (a.value.headD []);⟨r.value,a.work+r.work+8⟩
@[simp] theorem colorBits_value (T : BinaryProvider.Tree) (v : RMAF.Vertex) (x : Bits) :
 colorValue (colorBits T v x).value=VertexGeometry.colorLabel (treeValue T) v (decode x) := by
 simp [colorBits,VertexGeometry.colorLabel,blockValue,labelValue]
end GenericForest.BinaryProducer.Generator
