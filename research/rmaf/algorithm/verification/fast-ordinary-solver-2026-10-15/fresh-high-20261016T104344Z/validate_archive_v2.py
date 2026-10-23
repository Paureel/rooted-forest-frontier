#!/usr/bin/env python3
"""One-shot bounded archive replay; separates formal checks from resource failures."""
import gzip, hashlib, json, pathlib
here=pathlib.Path(__file__).resolve().parent
previous=json.loads((here/'FINAL-VALIDATION-v1.json').read_text())
archive=json.loads((here/'BODY-ARCHIVE-v3.json').read_text())
count=0
compressed_total=0
for record in archive['records']:
    whole=hashlib.sha256()
    size=0
    for chunk in record['chunks']:
        packed=(here/chunk['path']).read_bytes()
        assert hashlib.sha256(packed).hexdigest()==chunk['compressed_sha256']
        assert len(packed)==chunk['compressed_bytes']
        raw=gzip.decompress(packed)
        assert len(raw)==chunk['raw_bytes'] and len(raw)<=4*1024**2
        assert max(map(len,raw.splitlines()),default=0)<=8*1024**2
        assert hashlib.sha256(raw).hexdigest()==chunk['raw_sha256']
        whole.update(raw)
        size+=len(raw)
        compressed_total+=len(packed)
        count+=1
    assert size==record['raw_bytes'] and whole.hexdigest()==record['source_sha256']
assert compressed_total<=256*1024**2
out=dict(version=2,status='OPEN_SOURCE_BOUNDARY_AND_RESOURCE_POLICY',
         formal_component_checks_passed=previous['all_checks_passed'],
         full_literal_theorem_proved=False,counterexample_obtained=False,
         body_archive_replay_passed=True,body_chunks=count,compressed_bytes=compressed_total,
         historical_resource_controls_all_passed=False,
         resource_failures=['Names09 peak RSS above 3072 MiB','Stored proof AST exports above raw/line caps'],
         repaired_delivery_only=True,resource_policy_acceptance=False,
         independent_interface_review=False)
(here/'FINAL-VALIDATION-v2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
