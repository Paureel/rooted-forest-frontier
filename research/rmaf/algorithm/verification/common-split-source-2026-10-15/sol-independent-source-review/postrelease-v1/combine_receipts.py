#!/usr/bin/env python3
"""Lossless rows retained per producer; compact union avoids repeated module headers."""
import hashlib,json,pathlib,time
P=pathlib.Path(__file__).resolve().parent
order=json.loads((P/'SOURCE-HEADER-AUDIT-v1.json').read_text())['topological_order']
out=P/'ALL151-OCCURRENCES-v1.jsonl';assert not out.exists()
modules={};enc=None;occ=0;parts=0;start=time.perf_counter();encoders=0
with out.open('wb') as g:
 for m in order:
  with (P/'producer-rows'/(m+'.jsonl')).open('rb') as f:
   while line:=f.readline(32*1024*1024+1):
    if len(line)>32*1024*1024:raise ValueError('row cap exceeded')
    r=json.loads(line);tag=r['record']
    if tag=='encoder_controls':
     encoders+=1;digest=hashlib.sha256(line).hexdigest()
     if enc is None:enc=digest;g.write(line)
     else:assert enc==digest
    elif tag=='module':
     key=r['module'];value=r['olean_parts']
     if key in modules:assert modules[key]==value
     else:modules[key]=value;g.write(line)
    else:
     assert r['producer']==m
     if tag=='producer_part':parts+=1
     elif tag=='occurrence':occ+=1
     else:raise ValueError('unexpected record')
     g.write(line)
summary={'scientific_producers':len(order),'scientific_parts':parts,'stored_occurrences':occ,'module_headers':len(modules),'all_encoder_blocks_equal':encoders==151,'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'seconds':time.perf_counter()-start,'scope':'all occurrence and producer-part rows byte-preserved; redundant consistent module/encoder headers deduplicated; original perproducer receipts remain exact'}
assert summary['stored_occurrences']==4238 and parts==151 and encoders==151
(P/'COMBINED-RECEIPT-SUMMARY-v1.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
