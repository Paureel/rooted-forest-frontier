import hashlib,json
from pathlib import Path
P=Path('research/rmaf/monitoring/resume-complete-proof-20261022')
# Prospective metadata controls only; these do not validate mathematical content.
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
assert hashlib.sha256(b'abd').hexdigest()!='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
packets=[('final-cold-proposed-proof-public-v1','9d5dc341b4884946c7099785bcb918ce49246d7d9eda2e4dd161288ad4583044',28),('selected-paid-prepare-public-v1','c2a34a2c1817073324d8c723b75ac0136bfb5ea5af6cd4bf735c60285073b2de',2)]
rows=[]
for name,pin,count in packets:
 p=P/name;m=p/'FILES-v1.json';assert hashlib.sha256(m.read_bytes()).hexdigest()==pin
 fs=json.loads(m.read_text())['files'];assert len(fs)==count
 for f in fs:
  b=(p/f['name']).read_bytes();actual=hashlib.sha256(b).hexdigest()
  assert actual==f['sha256'] and len(b)==f['bytes'],f['name']
  rows.append(dict(packet=name,name=f['name'],sha256=actual,bytes=len(b)))
print(json.dumps(dict(metadata_controls=2,matched_files=len(rows),matched_packet_manifests=2,files=rows),indent=2))
