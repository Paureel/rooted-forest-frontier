#!/usr/bin/env python3
"""One-shot lossless storage for very repetitive actual producer Expr dumps.
Full type/body bytes are retained in gzip, with streamed SHA roundtrip checks.
This changes storage only; original receipts/proof/control records stay intact.
"""
from pathlib import Path
import datetime,gzip,hashlib,json,time
D=Path(__file__).resolve().parent;ROOT=D.parents[4]
rows=[]
for folder in sorted((ROOT/'results').glob('algorithm-universal233-rule4-replay-*')):
 raw=folder/'occurrences.json'
 if not raw.exists():continue
 start=time.monotonic();dest=folder/'occurrences.json.gz';h=hashlib.sha256();size=0
 with raw.open('rb') as src,dest.open('wb') as file,gzip.GzipFile(fileobj=file,mode='wb',compresslevel=1,mtime=0) as target:
  while block:=src.read(1024*1024):h.update(block);size+=len(block);target.write(block)
 original=h.hexdigest();verify=hashlib.sha256();decoded=0
 with gzip.open(dest,'rb') as src:
  while block:=src.read(1024*1024):verify.update(block);decoded+=len(block)
 assert verify.hexdigest()==original and decoded==size,'LOSSLESS_ROUNDTRIP_FAILED'
 packed=hashlib.sha256()
 with dest.open('rb') as src:
  while block:=src.read(1024*1024):packed.update(block)
 row={'source_name':'occurrences.json','stored_archive':'occurrences.json.gz','source_bytes':size,'source_sha256':original,'archive_bytes':dest.stat().st_size,'archive_sha256':packed.hexdigest(),'lossless_roundtrip_sha256_match':True,'seconds':round(time.monotonic()-start,6),'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'meaning':'Full actual ConstantInfo kind/type/body/direct refs/axiom refs preserved exactly. Decompress to recover the exact producer audit JSON; no scientific count or verdict changed.'}
 (folder/'occurrence-storage.json').write_text(json.dumps(row,indent=2)+'\n')
 # Generated, unfrozen serialization only; the archive reconstructs every byte.
 raw.unlink();rows.append({'receipt':str(folder.relative_to(ROOT)),**row})
 print(folder.name,size,'->',dest.stat().st_size,'bytes; SHA roundtrip exact.',flush=True)
if not (D/'RULE4-MANIFEST-v1.json').exists():
 (D/'OCCURRENCE-STORAGE-v1.json').write_text(json.dumps(rows,indent=2)+'\n')
