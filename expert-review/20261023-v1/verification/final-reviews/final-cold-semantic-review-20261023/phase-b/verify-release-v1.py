"""One-shot screened-release metadata receipt; no candidate execution."""
import hashlib
import json
from pathlib import Path

root = Path('/Users/paurel/Documents/ChatGPT/bootscience')
release_path = root / 'research/rmaf/monitoring/resume-complete-proof-20261022/FINAL-COLD-SEMANTIC-COMPUTATION-RELEASE-v1.json'
expected_release = '03c1aa4ff16dbcd03cb2474adc7ea3a2daed96ae79258b22b211ba1f5d3929e8'
digest = lambda raw: hashlib.sha256(raw).hexdigest()
assert digest(b'abc') == 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
assert digest(b'abd') != digest(b'abc')
raw = release_path.read_bytes()
assert digest(raw) == expected_release
release = json.loads(raw)
records = []
for packet in release['licensed_packets']:
    manifest = root / packet['manifest']
    manifest_actual = digest(manifest.read_bytes())
    assert manifest_actual == packet['manifest_sha256']
    records.append({'path': str(manifest), 'sha256': manifest_actual, 'kind': 'manifest'})
    for item in packet['licensed_files']:
        path = root / packet['licensed_directory'] / item['name']
        data = path.read_bytes()
        measured = digest(data)
        assert measured == item['sha256'] and len(data) == item['bytes'], str(path)
        records.append({'path': str(path), 'sha256': measured, 'bytes': len(data), 'kind': 'licensed'})
assert sum(row['kind'] == 'licensed' for row in records) == 38
out = Path(__file__).parent / 'RELEASE-INTEGRITY-v1.json'
assert not out.exists()
out.write_text(json.dumps({'release_sha256': expected_release, 'licensed_files': 38,
                           'records': records, 'hash_controls': 'abc positive / abd mismatch'}, indent=2) + '\n')
print('RELEASE_METADATA_MATCHED licensed=38/38 manifests=2/2 sha256_known_answer_and_mismatch=2/2')
