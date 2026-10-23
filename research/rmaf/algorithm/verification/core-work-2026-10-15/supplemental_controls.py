from pathlib import Path
import json,hashlib,datetime
b=Path(__file__).resolve().parent
controls={
'ReviewCostClean':'''import ReviewCostBridgeV4
import Controls
open RMAF Universal233.CoreProgram Universal233.CoreWork
namespace ReviewSourceUnit
 def comb : Nat → Tree | 0 => .leaf 0 | n+1 => .node (comb n) (.leaf (n+1))
 theorem helper_literal : groupsWork (fromTree id [] (comb 7)) = 79 := by decide
 theorem source_minimum : (15+8+2*28+7 : Nat) = 86 := by decide
 theorem wide_literal : reviewWideSheet 1 0 0 = 491 := by decide
 theorem wide_prune : reviewWideEnvelope 0 256 = 266 := by decide
 #print axioms helper_literal
 #print axioms source_minimum
 #print axioms wide_literal
 #print axioms wide_prune
end ReviewSourceUnit
''',
'ReviewCostFalse':'''import ReviewCostClean
open RMAF Universal233.CoreProgram Universal233.CoreWork ReviewSourceUnit
 theorem false_helper_is_fine_unit_upper : 86 ≤ groupsWork (fromTree id [] (comb 7)) := by decide
''',
'ReviewCostFalseZero':'''import ReviewCostClean
 theorem false_local_work_free : reviewWideSheet 1 0 0 = 0 := by decide
'''}
rows=[]
for n,s in controls.items():
 p=b/'isolated'/(n+'.lean');p.write_text(s);rows.append({'module':n,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'expectation':'compile0' if n=='ReviewCostClean' else 'nonzero explicit decide-is-false'})
pin={'phase':'supplemental post-candidate unit-conversion diagnostics, frozen before execution; does not replace29/61 preregistered controls','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'controls':rows,'literal_witness':{'left_comb_leaves':8,'tree_matches':15,'singleton_cons':8,'copied_left_cells':28,'append_base_matches':7,'minimum_fine_operations':86,'helper_groupsWork':79},'independent_replications_added':0}
(b/'SUPPLEMENTAL-CONTROL-PIN.json').write_text(json.dumps(pin,indent=2)+'\n');print(json.dumps(pin))
