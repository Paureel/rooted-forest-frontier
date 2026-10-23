from pathlib import Path
import json,hashlib,datetime
b=Path(__file__).resolve().parent
sources={
'WholeReviewSupplementClean':'''import WholeReviewSourceBounds
import WorkControls
open RMAF VertexGeometry Universal233.CoreProgram Universal233.WholeSourceWork
 def sixteen : Owned := ⟨List.replicate 16 ⟨[[0]],[]⟩,0,0,0,0⟩
 def one : Owned := ⟨[⟨[[1]],[]⟩],0,0,0,0⟩
 theorem actual_copy16 : (appendOwned sixteen one).copied = 16 := by decide
 theorem formal_append18 : (appendOwned sixteen one).work = 18 := by decide
 theorem minimal_fine33 : (2*16+1 : Nat) = 33 := by decide
 theorem source_contract128 : (8*16 : Nat) = 128 := by decide
 def fixtureTarget : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
 theorem selector_returns_root : (meterCliqueSelection fixtureTarget [0,3] [1,4] [2,5]).value = some [] := by decide
 #print axioms actual_copy16
 #print axioms formal_append18
 #print axioms selector_returns_root
''',
'WholeReviewFalseAppendUnit':'''import WholeReviewSupplementClean
open Universal233.WholeSourceWork
 theorem false_outer_meter_covers_fine_units : 33 ≤ (appendOwned sixteen one).work := by decide
''',
'WholeReviewFalseDispatch':'''import WholeReviewSupplementClean
open Universal233.WholeSourceWork
 theorem false_selector_result_is_arbitrary_supplied_vertex :
   (meterCliqueSelection fixtureTarget [0,3] [1,4] [2,5]).value = some [false,false,false] := by decide
'''}
rows=[]
for n,s in sources.items():
 p=b/'isolated'/(n+'.lean');p.write_text(s);rows.append({'module':n,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'expectation':'success' if n.endswith('Clean') else 'nonzero-explicit-decide-false'})
x={'phase':'supplemental post-release controls pinned before execution; readiness34/93 unchanged','controls':rows,'outer_witness':{'left_cells':16,'formal_append_work':18,'minimum_match_and_cons_plus_base':33,'contract8_cell_bill':128},'selector_witness':{'selected':'','separately_supplied_unrelated_vertex':'000','interface':'cliqueConstruction accepts v without equation to selector result; no false whole-algorithm assertion'},'added_replications':0}
(b/'SUPPLEMENTAL-CONTROL-PIN.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
