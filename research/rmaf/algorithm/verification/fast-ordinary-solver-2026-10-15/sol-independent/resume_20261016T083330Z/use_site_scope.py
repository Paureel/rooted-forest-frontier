"""One-shot formal direct-consumer footprint of the released public interfaces.
Reuses own stored rows and calibrated parser; no author auditor is executed.
A dependency footprint locates proof uses; semantic premise ruling stays scoped
and is written separately in INTERFACE-TRACE-v1.md.
"""
import copy,hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent;OLD=HERE.parent/'postrelease-v1'
sys.path.insert(0,str(HERE));sys.path.insert(0,str(OLD))
import resume_collect
from row_audit_metadata import rows
from scan_rows import read_label

def consumers(ds,name):
 return [{'consumer':n,'module':r['module'],'kind':r['kind'],'reference_fields':[f for f in ['type_refs','body_refs','extra_refs'] if name in r[f]]} for n,r in sorted(ds.items()) if any(name in r[f] for f in ['type_refs','body_refs','extra_refs'])]
def main():
 ds,_=rows(read_label('fixed-clean'));want='PrecontactClean.helper'
 assert [r['consumer'] for r in consumers(ds,want)]==['PrecontactClean.consumer']
 bad=copy.deepcopy(ds);bad['PrecontactClean.consumer']['body_refs']=[]
 assert consumers(bad,want)==[]
 # Both positive proof-only dependency and its deliberate omission were observed.
 old=resume_collect.old;old.read_label=resume_collect.route
 rr,_=old.load_phase('cold');ds,info=rows(rr)
 manifest=HERE.parents[6]/'unavailable'
 package=HERE.parents[4]/'universal233/ordinary_dispatch/fast_ordinary_recursion/FINAL-MANIFEST-v1.json'
 # Resolve only the already licensed original manifest via known workspace root.
 base=HERE.parents[7]
 package=base/'research/rmaf/algorithm/universal233/ordinary_dispatch/fast_ordinary_recursion/FINAL-MANIFEST-v1.json'
 names=json.loads(package.read_text())['interfaces']
 footprint={}
 for short in names:
  name='OrdinaryDispatch.FastOrdinary.'+short;assert name in ds,name
  r=ds[name]
  footprint[name]={'declaration_module':r['module'],'type':r['type'],'levels':r['levels'],'kind':r['kind'],'row_sha256':hashlib.sha256(old.canonical(r)).hexdigest(),'direct_custom_consumers':consumers(ds,name)}
 data={'status':'FORMAL-DIRECT-CONSUMER-FOOTPRINT','interfaces':len(footprint),'fixed_entrypoint':'FastExact','custom_declaration_denominator':len(ds),'footprint':footprint,'known_answer_proof_only_dependency_detected':True,'deliberate_dependency_removal_changes_result':True,'all_transitive_semantic_premises_independently_rederived':False,'independent_universal_reconstruction':False,'new_replication_credit':False,'sidecar_additional_consumer':{'source':str(OLD/'evaluator/IndependentInterface.lean'),'line':57,'caller':'IndependentReview.external_contract','consumed':'OrdinaryDispatch.FastOrdinary.external_exact','classification':'interface theorem consuming author universal theorem'}}
 with (HERE/'USE-SITE-SCOPE-v1.json').open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
 print(json.dumps({'interfaces':len(footprint),'custom_declaration_denominator':len(ds),'direct_consumer_links':sum(len(r['direct_custom_consumers']) for r in footprint.values()),'independent_universal_reconstruction':False}))
if __name__=='__main__':main()
