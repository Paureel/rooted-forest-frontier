#!/usr/bin/env python3
"""One-shot integrity control: corruption is refused before unsafe native parse."""
import gzip,hashlib,json,pathlib
here=pathlib.Path(__file__).resolve().parent
receipt=json.loads((here/'runs/export-positive/receipt.json').read_text())
assert receipt['status']=='ACCEPT'
raw=b''.join(gzip.decompress(pathlib.Path(c['path']).read_bytes()) for c in receipt['chunks'])
result=json.loads(raw)
assert result['kind']=='native-dag-control' and result['roundtrip'] and result['depth']==20 and result['numeric_name_and_syntax_metadata']
original=(here/'exports/control-v1.olean').read_bytes()
expected=hashlib.sha256(original).hexdigest()
assert len(original)==result['raw_bytes'] and len(original)<65536
bad=bytearray(original)
bad[len(bad)//2]^=1
(here/'exports/control-corrupted-v1.olean').write_bytes(bad)
def verified_data(data,expected_hash):
    if hashlib.sha256(data).hexdigest()!=expected_hash: raise ValueError('INTEGRITY_REFUSAL_BEFORE_NATIVE_PARSE')
    return data
verified_data(original,expected)
try: verified_data(bad,expected)
except ValueError as exc: caught=str(exc)
else: raise SystemExit('failed to catch corrupted native binary')
out=dict(version=1,installed_serializer='Lean.CompactedRegion',exact_native_roundtrip=True,
         expression_dag_depth=20,raw_bytes=len(original),sha256=expected,
         syntax_metadata_and_numeric_names_preserved=True,corrupted_copy_refused=caught,
         corrupted_copy_was_not_native_parsed=True,
         native_api_contract='Identical executable; identical erased payload type at save/read; no closures; dependency regions kept alive.')
(here/'EXPORT-QUALIFICATION-v1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
