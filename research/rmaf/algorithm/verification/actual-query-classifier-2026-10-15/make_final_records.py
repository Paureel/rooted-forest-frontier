from pathlib import Path
import json,hashlib,re,collections,datetime
b=Path(__file__).resolve().parent;root=b.parents[4]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((b/'CANDIDATE-PIN.json').read_text())
inventory={'scope':'Every declaration by actual originating positive source module, all constant kinds/private/generated, full transitive axiom closure.65 candidate/dependency modules; own audit/adapter/plants excluded.','lineage_extra_replications':0,'packages':{}}
for label in ['query','rank']:
 r=json.loads((b/('REPLAY-'+label.upper()+'.json')).read_text())
 inventory['packages'][label]={'positive_modules':r['positive_order'],'count':r['declarations'],'private_count':r['private'],'module_counts':r['module_counts'],'kind_counts':dict(collections.Counter(x['kind'] for x in r['origins'])),'axiom_union':r['axiom_union'],'all_declarations':r['origins']}
(b/'AXIOM-INVENTORY.json').write_text(json.dumps(inventory,indent=2)+'\n')
targets={'query':{'Caller':['def knownCost','def pending','def answerCost','def run','def allocated','def schedule'],'Specification':['def Planned','theorem run_sound','theorem run_complete','theorem schedule_sound','theorem schedule_complete','theorem schedule_accepts_iff'],'Budgets':['def badSlots','theorem allocation_paid_identity','theorem sole_hard_no_discount'],'Mass':['def actualQueryMass','theorem actual_paid_query_mass'],'Work':['def meterSchedule','theorem meterSchedule_value','theorem meterSchedule_caller','theorem meterSchedule_trace']},'rank':{'RankCost':['def inputRank','def RankFeasible'],'Probe':['def probe','theorem probe_nonempty_iff','theorem accepted_literal_stable','theorem rejected_cost_mass'],'FourProbe':['def fourProbe','def optimizedFourOutputs','theorem optimized_four_exact','theorem four_rejected_high'],'OptimizedWork':['def meterOptimizedFour','theorem meterOptimizedFour_calls','theorem meterOptimizedFour_bound'],'ProbeWork':['theorem probe_model_work'],'ColorBudget':['def dedupNat'],'SourceBridge':['noncomputable def checkedSourcePartition','theorem sourcePartition_from_checks'],'ColorClasses':['theorem rank_partition_color_classes'],'SourceValidity':['theorem generated_source_valid']}}
read=[]
for label,modules in targets.items():
 for mod,starts in modules.items():
  p=b/('isolated-'+label)/(mod+'.lean');lines=p.read_text().splitlines()
  for start in starts:
   indices=[i for i,l in enumerate(lines) if l.startswith(start+' ') or l==start]
   assert len(indices)==1,(label,mod,start)
   i=indices[0];j=i+1
   while j<len(lines) and lines[j].strip() and j<i+12:j+=1
   read.append({'grade':'READ source statement; proof/interface interpretation separately in CONSUMER-TRACE','source':str(p.relative_to(root)),'source_sha256':h(p),'line':i+1,'declaration':start,'verbatim':'\n'.join(lines[i:j])})
contacts={'phase':'Exact root release only after immutable60 readiness','ready_manifest_sha256':h(b/'READY-ARTIFACTS.json'),'author_manifests':{k:v['manifest_sha256'] for k,v in pin['packages'].items()},'read_statement_records':read,'source_copy_contacts':{k:v['copied_sources'] for k,v in pin['packages'].items()},'read_author_prose':['research/rmaf/algorithm/universal233/query_scheduler/RESULT.md','research/rmaf/algorithm/universal233/query_scheduler/COST-MODEL.md','research/rmaf/algorithm/universal233/query_scheduler/FIRST-GAP.md','research/rmaf/algorithm/universal233/rank_consumer/RESULT.md','research/rmaf/algorithm/universal233/rank_consumer/INTERFACE.md','research/rmaf/algorithm/universal233/rank_consumer/FIRST-GAP.md'],'read_canonical_receipts':[v['canonical_receipt'] for v in pin['packages'].values()],'inferred_records':['SOURCE-COST-REVIEW explicit128 linear source envelope,64 fixed inspection,bit/oracle/serialization contracts','CONSUMER-TRACE hypothesis/actual-interface interpretations','Candidate tail-first rank dedup10 comparisons from literal recursion; instrument first-seen16 retained'],'background_unverified':'none used for a supported mathematical claim','audit_metadata':'All65 source modules rebuilt and originating declarations inventoried; selected executable/proof consumer sources manually read. No claim of independent rederivation of every completed dependency theorem.','excluded':['author audit/replay implementation','live maf_scheduler/depth/cherry/groupedforest/binarygeometry and fresh-reviewer content','scientific author oleans'],'noted_noncontent_event':'Attempt to read nonexistent rank_consumer/SOURCE-COST-MODEL.md returned file-not-found; no scientific inference drawn','lineage_extra_replications':0,'author_child_contact':False}
(b/'CANDIDATE-SOURCE-READ-LEDGER.json').write_text(json.dumps(contacts,indent=2)+'\n')
clauses=[
 ('QUERY-VALUES','CONFIRMED-SCOPED','common original-p budget,first failure,final total,duplicates','Caller.lean:32','ACTUAL-COMPARISON.json'),
 ('QUERY-EXACTNESS','CONFIRMED-SCOPED','Planned plus exact-minimum/valid-witness success IH and budget completeness IH','Specification.lean:193','CONSUMER-TRACE.md'),
 ('QUERY-MASS','CONFIRMED-SCOPED','actual failed/success calls;rational c>=2;badSlots>=2','Mass.lean:121','ACTUAL-COMPARISON.json'),
 ('QUERY-METER','CONFIRMED-SCOPED','exact meter projection/trace and32(n+1) declared meter arithmetic','Work.lean:82','REPLAY-QUERY.json'),
 ('SC32','OPEN-AT-NAMED-OBLIGATION','32 every-fine-source-operation interpretation not established; independent128 source inspection preservesO(n)','SOURCE-COST-REVIEW.md','POST-CANDIDATE-SCOPE-RECEIPT.json'),
 ('FOUR-LIST','CONFIRMED-SCOPED','proper original labels and rank4;actual full raw list equality','FourProbe.lean:25','ACTUAL-COMPARISON.json'),
 ('FOUR-HIGH-MASS','CONFIRMED-SCOPED','actual probe rejection;c>=2;allcost>=4;rawLIST<=2c^-4','FourProbe.lean:45','ACTUAL-COMPARISON.json'),
 ('FOUR-WORK','CONFIRMED-SCOPED','corrected core source contracts;64 setup inspection;all callback bills and bit/serialization additional','OptimizedWork.lean:44','SOURCE-COST-REVIEW.md'),
 ('OWN-OPTIMUM-DISCOUNT','REFUTED-AT-WITNESS','sole-hardknown0,min5,q5hasbudget5andmass1','ACTUAL-QUERY.log','MASS-CONTROL-PIN-v1.json'),
 ('NO-RANK4-EXACTNESS','REFUTED-AT-WITNESS','oneleafcolor0q0optimizedemptyversusactualsingleton','isolated-rank/ReviewScope.lean:4','logs-rank/ReviewFalseScope.log'),
 ('NO-IH-EXACTNESS','REFUTED-AT-WITNESS','bogus(0,999)accepted andalwaysfailrejectsfeasiblemock','isolated-query/ReviewScope.lean:6','logs-query/ReviewScope.log'),
 ('QUERY-IH','OPEN-AT-NAMED-OBLIGATION','actualrecursiveMAFsolverandvalidminimumwitnessIH','Specification.lean:193','CONSUMER-TRACE.md'),
 ('QUERY-SLOTS','OPEN-AT-NAMED-OBLIGATION','originalstateexactpretestslots,disjointrestriction/reconstruction','Caller.lean:50','CONSUMER-TRACE.md'),
 ('FOUR-INPUT','OPEN-AT-NAMED-OBLIGATION','mainoriginalparent/sectorcallerinstantiatesrank4','FourProbe.lean:26','CONSUMER-TRACE.md'),
 ('PAID-COMPOSITION','OPEN-AT-NAMED-OBLIGATION','actualpair/sourceconsumerdischargesother-slotpayment','Mass.lean:123','CONSUMER-TRACE.md'),
 ('GLOBAL-PROGRESS','OPEN-AT-NAMED-OBLIGATION','stateprogress,termination,totalqueryrecurrenceandcompletealgorithm/runtime','RESULT.md','CONSUMER-TRACE.md')]
(b/'CLAIM-VERDICTS.json').write_text(json.dumps({'all_three_main_milestones':'OPEN','additional_independent_replications':0,'claims':[dict(zip(['claim','verdict','scope','locator','evidence'],x)) for x in clauses]},indent=2)+'\n')
print(json.dumps({'origin_inventories':{k:v['count'] for k,v in inventory['packages'].items()},'read_statement_locators':len(read),'scoped_claims':len(clauses)}))
