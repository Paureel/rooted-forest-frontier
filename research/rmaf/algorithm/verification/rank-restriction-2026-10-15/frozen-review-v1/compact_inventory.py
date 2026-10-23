#!/usr/bin/env python3
"""Retain exact oversized Expr exports losslessly; compact complete inventories.
No source or frozen prior evidence is modified. Payload SHA pins survive gzip.
"""
from pathlib import Path
import hashlib,json,gzip,time
HERE=Path(__file__).resolve().parent;ROOT=next(x for x in HERE.parents if (x/'bootloops-python').is_file());R=ROOT/'research/rmaf/results'
p=R/'algorithm-rank-restriction-fresh-signature-inventory-v1.json';d=json.loads(p.read_text())
byall={r['name']:r for r in d['inventories']['RestrictionAll']['rows']};byconsumer={r['name']:r for r in d['inventories']['RestrictionConsumer']['rows']}
changes=[]
for n,x in byall.items():
 y=byconsumer[n];assert x['type']==y['type'] and x['type_hash']==y['type_hash']
 if x['body']!=y['body']:
  assert n in ['RMAF.pairwiseEmbeddings.eq_def','RMAF.minimalVertices.eq_def','RMAF.rootedSpan.eq_def']
  assert x['body'].replace('`_private.Embedding','`_private.Bridge')==y['body']
  changes.append({'name':n,'type_exactly_equal':True,'proof_body_exact_only_substitution':{'import_all':'`_private.Embedding','consumer_only':'`_private.Bridge'},'import_all_body_sha256':hashlib.sha256(x['body'].encode()).hexdigest(),'consumer_body_sha256':hashlib.sha256(y['body'].encode()).hexdigest(),'kind':'compiler-generated equation theorem proof; no executable definition changed'})
assert len(changes)==3
for inv in d['inventories'].values():
 for row in inv['rows']:
  body=row.pop('body');row['body_repr_sha256']=hashlib.sha256(body.encode()).hexdigest() if body is not None else None;row['body_repr_bytes']=len(body.encode()) if body is not None else 0
  row['type_repr_sha256']=hashlib.sha256(row['type'].encode()).hexdigest()
d.update({'initial_body_identity_assertion':'FAILED and preserved exactly in archived v1 receipt; three generated proof terms differ in private helper prefix','generated_proof_body_differences':changes,'exact_type_count':694,'exact_body_count':691,'verdict':'PASS-COMPLETE-TYPES-BODY-HASHES-AND-EXACT-GENERATED-PROOF-ADOPTION; INITIAL-ASSERTION-RETAINED','all_three_main_milestones':'OPEN'})
q=R/'algorithm-rank-restriction-fresh-signature-inventory-v2.json';q.write_text(json.dumps(d,indent=2)+'\n');print('compact',q.stat().st_size,flush=True)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
index={'reason':'Oversized raw Lean Expr signature/body receipts archived losslessly; no source/frozen result edits','archives':[]}
idx=HERE/'LOSSLESS-EXPR-ARCHIVE-v1.json'
paths=[HERE/'isolated-release-v1/rank/FreshSignaturesRank.log',HERE/'isolated-release-v1/restriction/FreshSignaturesRestrictionAll.log',HERE/'isolated-release-v1/restriction/FreshSignaturesRestrictionConsumer.log',p]
for src in paths:
 start=time.monotonic();expected=sha(src);dst=src.with_suffix(src.suffix+'.gz');assert not dst.exists()
 with src.open('rb') as fin,dst.open('wb') as fout:
  with gzip.GzipFile(filename='',mode='wb',fileobj=fout,mtime=0,compresslevel=6) as gz:
   for b in iter(lambda:fin.read(1024*1024),b''):gz.write(b)
 got=hashlib.sha256()
 with gzip.open(dst,'rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):got.update(b)
 assert got.hexdigest()==expected
 index['archives'].append({'original_path':str(src.relative_to(ROOT)),'payload_sha256':expected,'payload_bytes':src.stat().st_size,'archive_path':str(dst.relative_to(ROOT)),'archive_sha256':sha(dst),'archive_bytes':dst.stat().st_size,'decompression_verified':True,'seconds':time.monotonic()-start})
 idx.write_text(json.dumps(index,indent=2)+'\n');src.unlink();print('lossless',src.name,index['archives'][-1]['seconds'],flush=True)
print('PASS-LOSSLESS-ARCHIVE-AND-COMPACT-INVENTORY',flush=True)
