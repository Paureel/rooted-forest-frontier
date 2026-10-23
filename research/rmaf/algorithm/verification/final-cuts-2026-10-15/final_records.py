from pathlib import Path
import json,hashlib,collections
b=Path(__file__).resolve().parent;root=b.parents[4];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
replay=json.loads((b/'REPLAY.json').read_text());prov=json.loads((b/'PROVENANCE-MAP.json').read_text())
inventory={'status':'COMPLETE-ACTUAL-ORIGIN-AXIOM-INVENTORY','source_modules':62,'origin_declarations':2719,'private_names':249,'kind_counts':dict(collections.Counter(x['kind'] for x in replay['all_origin_records'])),'axiom_union':replay['axiom_union'],'all_declarations':replay['all_origin_records'],'exact_source_adoption_map_sha256':h(b/'PROVENANCE-MAP.json'),'scope':'All62 scientific modules incl unused imports,generated/private/constructors/recursors. Deliberate own controls and author interface/audit/plant modules excluded,not hidden as accepted scientific modules.','extra_replications':0};(b/'AXIOM-INVENTORY.json').write_text(json.dumps(inventory,indent=2)+'\n')
targets={'RecoveryProgram':['def blockColor','def inputCheck','def recover'],'BlockColors':['theorem checked_flatten_nodup','theorem checked_rank','theorem checked_separation'],'Permutations':['def BlockPermutation','theorem checked_block_permutation','theorem agreement_block_permutation'],'Recovery':['theorem recover_checked','theorem recover_sound','theorem recover_edges','theorem recover_success_iff','theorem recover_original_agreement','theorem accepted_guards'],'FinalWork':['def guardCharge','def colorCharge','def meterColor','theorem meterColor_work','theorem total_color_work','def meterRecover','theorem meterRecover_value','theorem checked_flatten_perm','def finalPolynomial','theorem final_work_bound','theorem final_work_actual_cost','theorem final_work_absorbed'],'OriginalGraph':['def ResidualAdj'],'Realization':['def RealizedOutput']};read=[]
for mod,starts in targets.items():
 p=b/'isolated'/(mod+'.lean');lines=p.read_text().splitlines()
 for text in starts:
  indices=[i for i,l in enumerate(lines) if l.startswith(text+' ')];assert len(indices)==1,(mod,text);i=indices[0];j=i+1
  while j<len(lines) and lines[j].strip() and j<i+18:j+=1
  read.append({'grade':'READ copied actual source statement; proof/consumer interpretation in CONSUMER-TRACE','source':str(p.relative_to(root)),'sha256':h(p),'line':i+1,'declaration':text,'verbatim':'\n'.join(lines[i:j])})
interface=(b/'isolated/Interfaces.lean').read_text();assert all(not x.strip() or x.startswith('import ') or x.startswith('#check ') for x in interface.splitlines())
ledger={'phase':'root exact release AFTER55 immutable readiness entries','author_manifest_sha256':'95569c46912bff25f74cd01174bc51a934e7395524922271e6de4538fbdc4fb3','statement_records':read,'primary_canonical_import_body_map':'PROVENANCE-MAP.json','all_origin_inventory':'AXIOM-INVENTORY.json','read_author_prose':['RESULT.md','COST-MODEL.md','INTERFACE.md','FIRST-GAP.md'],'read_canonical_receipt':'results/algorithm-universal233-final-cuts-replay-20261015T105812Z/certificate.json','read_bound_result':'results/algorithm-universal233-final-cuts-20261015T105907Z.json','interface_printer_inspected':'Actual source contains only import FinalRegression and18 #check lines,no declarations; not executed/reused','inferred_not_kernel_extracted':['SOURCE-COST-REVIEW conservative guard/color/source correspondence','semantic actual original-graph interpretation and remaining main-call obligations','accepted bit-cost model and serialization interpretation'],'background_unverified':'none used to support a mathematical conclusion','candidate_negative_controls':'4 rejected explicit false propositions; excluded from positive modules','forbidden_contacts':'none; no live main/allgood/genericforest/outputstate or other fresh-reviewer implementation; no author/child contact','same_lineage_extra_replications':0,'fresh_context_prose_referee':'PENDING separate root assignment,no self-credit'};(b/'CANDIDATE-READ-LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
claims=[
 ('RECOVER-EXEC','CONFIRMED-SCOPED','isolated/RecoveryProgram.lean:9','Three actual guards, original generate at p-1 and head; 22 fixtures.'),
 ('RANK-CLASSES','CONFIRMED-SCOPED','isolated/BlockColors.lean:55','Actual P partition check derives rank p and full classes; no runtime oracle.'),
 ('P-PERMUTATIONS','CONFIRMED-SCOPED','isolated/Permutations.lean:9','Actual List.Perm at outer and inner levels, with multiplicity.'),
 ('ORIGINAL-REALIZATION','CONFIRMED-SCOPED','isolated/Realization.lean:29','All original vertices, both orientations, no leafless component, exact roots and cuts+1.'),
 ('EXACT-COST','CONFIRMED-SCOPED','isolated/Recovery.lean:27','Returned original cut cost p-1; guarded Nat budget.'),
 ('ORIGINAL-AF-TRANSPORT','CONFIRMED-SCOPED','isolated/Recovery.lean:87','Actual original agreement and source Nodup required.'),
 ('FINAL-WORK','CONFIRMED-SCOPED','isolated/FinalWork.lean:116','Kernel meter algebra plus separate corrected source inspection and contracts.'),
 ('ONCE-ABSORPTION','CONFIRMED-SCOPED','isolated/FinalWork.lean:165','One call, rational c>=2, k<=q; invocation count is external.'),
 ('SOURCE-IMPLIES-TARGET','REFUTED-AT-WITNESS','isolated/ReviewUse.lean:20','Source-valid crossed target has false agreement; explicit false control.'),
 ('UNIQUE-GRAPH-HISTORY','REFUTED-AT-WITNESS','CONTROL-PIN.json','Both pair cut certificates valid; raw singleton concerns deterministic code.'),
 ('LOCAL-CUT-SUBSTITUTION','REFUTED-AT-WITNESS','ACTUAL-COMPARISON.json','Original edge0 contains 012, prototype edge0 contains only0; whole certificate fails.'),
 ('DROP-LEAFLESS','REFUTED-AT-WITNESS','CONTROL-PIN.json','Pair cuts0 and1 leave a leafless original root component that must be counted.'),
 ('FREE-REPEATED-CHARGE','REFUTED-AT-WITNESS','isolated/ReviewFalseScope.lean:4','Eight charges of factor8 total64; this is not a tight runtime lower bound.'),
 ('MINIMUM-SELECTION','OPEN-AT-NAMED-OBLIGATION','CONSUMER-TRACE.md','Complete well-founded minimum AF selection.'),
 ('MAIN-CALL-ONCE','OPEN-AT-NAMED-OBLIGATION','CONSUMER-TRACE.md','Actual main caller supplies original AF, k<=q and one post-selection call.'),
 ('GLOBAL-RECURRENCE','OPEN-AT-NAMED-OBLIGATION','CONSUMER-TRACE.md','Complete query, state, restriction, assembly, progress and recurrence.'),
 ('MACHINE-RUNTIME','OPEN-AT-NAMED-OBLIGATION','SOURCE-COST-REVIEW.md','No extracted instruction, compiler or GC cost proof.'),
 ('FRESH-CONTEXT-REVIEW','OPEN-AT-NAMED-OBLIGATION','RESULT.md','Later separate prose/referee pass reserved by root; no self-credit.')]
(b/'CLAIM-VERDICTS.json').write_text(json.dumps({'claims':[dict(zip(['claim','verdict','locator','scope'],x)) for x in claims],'all_three_main_milestones':'OPEN','extra_replications':0},indent=2)+'\n')
print(json.dumps({'source_statement_locators':len(read),'claim_verdicts':len(claims),'declaration_records':len(inventory['all_declarations'])}))
