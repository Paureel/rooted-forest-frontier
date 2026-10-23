#!/usr/bin/env python3
"""One-shot copy/binding of expressly whitelisted public preparation records."""
import hashlib
import json
from pathlib import Path
import shutil
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
items=[
 ('research/rmaf/algorithm/verification/rule5-classification-2026-10-15/TARGET-v1.md','root-TARGET-v1.md'),
 ('research/rmaf/algorithm/verification/rule5-classification-2026-10-15/PUBLIC-DEFINITIONS-v1.json','PUBLIC-DEFINITIONS-v1.json'),
 ('research/rmaf/algorithm/verification/rule5-classification-2026-10-15/PUBLIC-DEFINITIONS-SUPPLEMENT-v2.json','PUBLIC-DEFINITIONS-SUPPLEMENT-v2.json'),
 ('research/rmaf/algorithm/verification/both-bad-2026-10-15/PUBLIC-DEFINITIONS-v1.json','both-bad-PUBLIC-DEFINITIONS-v1.json'),
 ('research/rmaf/algorithm/verification/ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md','ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md'),
]
for name in ['TARGET-v1.md','RESULT-v1.md','INTERFACE-v1.md','FIRST-GAP-v1.md','SOURCE-WORK-v1.md']:
    items.append(('research/rmaf/algorithm/universal233/rule5_classification/'+name,'classification-'+name))
directory=HERE/'public-inputs';directory.mkdir(exist_ok=True)
rows=[]
for name,alias in items:
    source,target=ROOT/name,directory/alias
    assert not target.exists()
    shutil.copyfile(source,target)
    assert target.read_bytes()==source.read_bytes()
    target.chmod(0o444)
    rows.append({'source':name,'copy':str(target.relative_to(HERE)),
                 'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'read_status':'read in full; retrieved public statements only'})
supplement=json.loads((directory/'PUBLIC-DEFINITIONS-SUPPLEMENT-v2.json').read_text())
assert hashlib.sha256((directory/'PUBLIC-DEFINITIONS-SUPPLEMENT-v2.json').read_bytes()).hexdigest()=='9eb4dd9a3040af5c3b5271524d542d835cabd50b6c6a7b62b7dae760d4c5f3f0'
for row in supplement['definitions']:
    assert hashlib.sha256(row['excerpt'].encode()).hexdigest()==row['excerpt_sha256']
source=ROOT/'research/rmaf/sources/baseline/split-or-decompose-v2.txt'
selected=[]
with source.open() as stream:
    for i,line in enumerate(stream,1):
        if i>1086:break
        if i>=950:selected.append(line)
target=directory/'Original-Lemma13-scaffold-lines950-1086.txt'
target.write_text(''.join(selected));target.chmod(0o444)
rows.append({'source':str(source.relative_to(ROOT)),'lines_1_based':[950,1086],
             'copy':str(target.relative_to(HERE)),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
             'read_status':'attributed original scaffold only; excluded remaining-case proof not read'})
skills=[]
for name in ['prove-protocol','reading-contract','independence-bookkeeping','planted-truth','timing-discipline','tool-stewardship','acceptance-gate','prose-lint']:
    path=ROOT/'.agents/skills'/name/'SKILL.md'
    skills.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                   'status':'applied; first seven read fully again in this arm, prose-lint read fully in preceding forest arm'})
data={'candidate_contact':False,'public_records':rows,'skills':skills,
      'capsule_source_correspondence':'excerpt digests checked; original barred module correspondence remains for exact release',
      'toolkit_guides':['bootloops/tools/README.md','bootloops/tools/gatekeeper/GUIDE.md']}
(HERE/'PUBLIC-READ-LEDGER-v1.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'copied_public_records':len(rows),'exact_supplement_excerpt_hashes':5,'classification_candidate_contacts':0}))
