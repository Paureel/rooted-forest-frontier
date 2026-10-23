#!/usr/bin/env python3
"""One-shot lossless bounded proof-body packaging; preserves failed raw exports.
The existing runner caps process logs, not JSON files emitted by a Lean command.
This packager repairs the delivery format, without deleting the oversized outputs.
"""
import gzip, hashlib, json, pathlib, time

here=pathlib.Path(__file__).resolve().parent
chunk_limit=4*1024**2
sources=['OWN-STORED-BODIES-v2.json','REUSED-STORED-BODIES-v2.json','DEPENDENCY-GRAPH-v2.json']
start=time.monotonic()
records=[]
total_compressed=0
pilot=None
for name in sources:
    chunks=[]
    full=hashlib.sha256()
    size=0
    with (here/name).open('rb') as source:
        index=0
        while True:
            block=source.read(chunk_limit)
            if not block: break
            full.update(block)
            size+=len(block)
            t=time.monotonic()
            packed=gzip.compress(block, compresslevel=6, mtime=0)
            elapsed=time.monotonic()-t
            if pilot is None: pilot=dict(raw_bytes=len(block),elapsed_seconds=elapsed,compressed_bytes=len(packed))
            total_compressed+=len(packed)
            if total_compressed > 256*1024**2: raise SystemExit('compressed cap exceeded')
            out=f'body-v3-{name.removesuffix(".json")}-{index:03}.jsonfrag.gz'
            with (here/out).open('xb') as target: target.write(packed)
            restored=gzip.decompress(packed)
            assert restored == block and len(restored)<=chunk_limit
            chunks.append(dict(path=out,raw_bytes=len(block),raw_sha256=hashlib.sha256(block).hexdigest(),
                               compressed_bytes=len(packed),compressed_sha256=hashlib.sha256(packed).hexdigest(),
                               compression_seconds=elapsed))
            index+=1
    records.append(dict(source=name,raw_bytes=size,source_sha256=full.hexdigest(),
                        restore='Concatenate decompressed chunks in this exact order, then parse UTF-8 JSON.',chunks=chunks))
out=dict(version=3,chunk_raw_limit=chunk_limit,raw_log_cap=16*1024**2,line_cap=8*1024**2,
         compressed_cap=256*1024**2,total_compressed_bytes=total_compressed,
         first_chunk_pilot=pilot,elapsed_seconds=time.monotonic()-start,
         prior_oversized_exports_preserved=True,records=records)
(here/'BODY-ARCHIVE-v3.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'}))
