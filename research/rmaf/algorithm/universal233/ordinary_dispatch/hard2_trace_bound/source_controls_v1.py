# One-shot fresh source-adaptation controls, reusing the frozen exact comparator.
from pathlib import Path
import ast, datetime, hashlib, json, re
D=Path(__file__).resolve().parent;R=D.parents[5]
S=D.parent/'hard2_dispatch/audit_hard2_v1.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(S)=='50079a7b8c9bac66db735d5f9f5b4a3557b55c3703af6807be348cd4bb610179'
f=[n for n in ast.walk(ast.parse(S.read_text())) if isinstance(n,ast.FunctionDef) and n.name=='adapt']
assert len(f)==1
exec(compile(ast.Module(body=f,type_ignores=[]),str(S),'exec'))
control='import TracePlantBase\n\nnamespace TracePlant\ndef value : Nat := 0\nend TracePlant\n'
want='import TracePlantAlias\n\nnamespace TracePlant\ndef value : Nat := 0\nend TracePlant\n'
assert adapt(control,{'TracePlantBase':'TracePlantAlias'})==want
try:assert adapt(control.replace(':= 0',':= 1'),{'TracePlantBase':'TracePlantAlias'})==want
except AssertionError:corrupt='CAUGHT'
else:raise AssertionError('BODY_CORRUPTION_ACCEPTED')
p=D/'SOURCE-CONTROLS-v1.json';assert not p.exists()
p.write_text(json.dumps(dict(status='PASS_FRESH_EXACT_SOURCE_CONTROLS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),same_author_lineage=True,inputs={str(Path(__file__).relative_to(R)):sha(Path(__file__)),str(S.relative_to(R)):sha(S)},exact_import_adaptation_blank_line='PASS',nonimport_body_corruption=corrupt,production_adaptations_in_this_extension=0),indent=2)+'\n')
print('PASS_FRESH_EXACT_SOURCE_CONTROLS',sha(p))
