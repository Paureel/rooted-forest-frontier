# One-shot metadata correction from existing exact producer records. No source,
# control, proof-data, or prior certificate is changed or regenerated.
from pathlib import Path
import gzip,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[6]
B=R/json.loads((D/'RESUME-BUILD-v1.json').read_text())['directory']
O=B/'author-source-audit-v2';P=O/'certificate.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads(P.read_text());assert c['status']=='PASS_AUTHOR_SOURCE_BOUND_ORDINARY_CALL_RECURRENCE'
full=[];qualified=[]
for e in c['new_producers']:
 p=R/e['path'];assert sha(p)==e['sha256']
 with gzip.open(p,'rt') as f:rows=json.load(f)
 scopes={r['body_text_scope'] for r in rows}
 if scopes=={'FULL_ALL_BODY'}:full.append(e['module'])
 else:
  assert scopes<={'FULL_NONPROOF_BODY','OMITTED_THEOREM_PROOF_TEXT'}
  qualified.append(e['module'])
amend=dict(version=1,source_certificate=str(P.relative_to(R)),source_certificate_sha256=sha(P),
 correction='The v2 field fresh_full_body_modules counted all fresh producers. Count the explicit saved body_text_scope values instead. Scientific result, bodies, references, axiom closure and controls are unchanged.',
 fresh_producer_modules=len(c['new_producers']),fresh_full_body_modules=len(full),qualified_proof_text_omission_modules=len(qualified),full_body_producers=full,qualified_producers=qualified,
 derivation_instrument=str(Path(__file__).relative_to(R)),derivation_instrument_sha256=sha(Path(__file__)))
A=O/'AUDIT-COUNTS-AMENDMENT-v1.json';assert not A.exists();A.write_text(json.dumps(amend,indent=2)+'\n')
c.update(fresh_producer_modules=len(c['new_producers']),fresh_full_body_modules=len(full),qualified_proof_text_omission_modules=len(qualified),metadata_amendment=str(A.relative_to(R)),metadata_amendment_sha256=sha(A),original_certificate_sha256=sha(P))
Q=O/'certificate-qualified-v3.json';assert not Q.exists();Q.write_text(json.dumps(c,indent=2)+'\n')
(D/'LATEST-AUDIT-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate=str(Q.relative_to(R)),certificate_sha256=sha(Q)),indent=2)+'\n')
print(c['status'],'full_body_modules',len(full),'qualified_modules',len(qualified),'axioms',c['axiom_union'])
