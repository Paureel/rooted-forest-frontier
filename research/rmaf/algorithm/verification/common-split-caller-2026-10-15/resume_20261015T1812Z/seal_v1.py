#!/usr/bin/env python3
"""One-shot final identity seal, no scientific re-execution or new claim."""
import json,os,time
from pathlib import Path
import continuation_v1 as c
P=c.P;PRE=c.PRE;POST=c.POST;ROOT=c.ROOT
checks=[]
for f,h,groups in [(P.parent/'ROOT-RELEASE-v1.json','baa70f84f0974e2f5767876cde7d846e61f8eb8f08ac7c8981226c3ea9d69f47',[]),(PRE/'READY-MANIFEST-v1.json','ffc6fe9b3c30f85f121979cc2b8a5492be2d7477d0863b9d7405adad927441d8',['files','permitted_inputs']),(c.M,'3da4d51890af8e552b9942667f0f61afff9f6def6af58073f8f1d05286f1714e',['immutable_files','external_input_pins'])]:
    assert c.sha(f)==h
    obj=json.loads(f.read_text())
    for group in groups:
        for r in obj[group]:
            q=ROOT/r['path'];assert q.stat().st_size==r['bytes']and c.sha(q)==r['sha256'],r['path']
        checks.append({'manifest':str(f.relative_to(ROOT)),'group':group,'matched':len(obj[group])})
    if 'files'in groups:assert all((ROOT/r['path']).stat().st_mode&0o222==0 for r in obj['files'])
build=json.loads((P/'INTEGRITY-BUILD-CORRESPONDENCE-v1.json').read_text())
for r in build['current_artifacts']:
    assert c.sha(POST/'scientific-src'/(r['module']+'.lean'))==r['source_sha256']
    assert c.sha(POST/f"build-{r['module']}-v1.log")==r['log_sha256']
    for a in r['artifacts']:assert (ROOT/a['path']).stat().st_size==a['bytes']and c.sha(ROOT/a['path'])==a['sha256']
c.write('FROZEN-RECHECK-v1.json',{'status':'MATCH','original139_read_only':True,'checks':checks,'all173_source_log_current_artifact_hashes_still_match':True,'new_scientific_builds':0})
cached={}
for f in P.glob('projected-prior-batch-*-v1.json'):
    r=json.loads(f.read_text());i=r['batch']
    for ext,key in [('json','json'),('log','log')]:cached[POST/f'producer-chunk-v3-{i}.{ext}']={'sha256':r['raw_'+key+'_sha256'],'bytes':r['raw_'+key+'_bytes'],'hash_record':'complete raw decoded projection comparison and full input hash earlier in this continuation; size rechecked at seal'}
reused=[]
for f in sorted(POST.rglob('*')):
    if not f.is_file()or'__pycache__'in f.parts or f.suffix=='.pyc':continue
    if f in cached:
        r=dict(cached[f]);assert f.stat().st_size==r['bytes']
    else:r={'bytes':f.stat().st_size,'sha256':c.sha(f),'hash_record':'seal-time complete bytes'}
    reused.append(dict(path=str(f.relative_to(ROOT)),**r))
for folder in [PRE/'origin/build-full-v2',PRE/'origin/private-imports']:
    for f in sorted(folder.rglob('*')):
        if f.is_file():reused.append({'path':str(f.relative_to(ROOT)),'bytes':f.stat().st_size,'sha256':c.sha(f),'hash_record':'seal-time complete bytes; exact prior control binary reused as trusted same-lineage fixture output'})
c.write('REUSED-POSTRELEASE-EVIDENCE-PINS-v1.json',{'same_lineage':True,'replication_credit':0,'scope':'all predecessor postrelease files preserved, plus exact reused original control build libraries; original READY139 separately rechecked; derived Python caches excluded','files':reused})
files=[]
for f in sorted(P.rglob('*')):
    if not f.is_file()or'__pycache__'in f.parts or f.name=='FINAL-MANIFEST-v1.json':continue
    files.append({'path':str(f.relative_to(ROOT)),'bytes':f.stat().st_size,'sha256':c.sha(f)})
c.write('FINAL-MANIFEST-v1.json',{'status':'QUALIFIED_SAME_LINEAGE_REVIEW_SEALED_FOR_ROOT_ADOPTION','files':files,'new_independent_replication_credit':0,'original_ready_sha256':'ffc6fe9b3c30f85f121979cc2b8a5492be2d7477d0863b9d7405adad927441d8','exact_candidate_sha256':'3da4d51890af8e552b9942667f0f61afff9f6def6af58073f8f1d05286f1714e','root_release_sha256':'baa70f84f0974e2f5767876cde7d846e61f8eb8f08ac7c8981226c3ea9d69f47','continuation_note_sha256':'a2ebcd1d2ef9c0040be446f0a4a249e6ec380ab0bda5eb1be66d708b0ffe24c8','main_milestones':'ALL_OPEN','compiled_runtime_IR_and_fine_source_bridge':'OPEN','fresh_context_framing':'SEPARATE_ROOT_STEP','all_local':True,'excluded_from_manifest':'derived Python caches only'})
print(json.dumps({'sealed_files':len(files),'reused_predecessor_files':len(reused),'manifest_sha256':c.sha(P/'FINAL-MANIFEST-v1.json'),'original_and_candidate_pins':'MATCH'}))
