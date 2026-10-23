#!/usr/bin/env python3
"""Packaging/provenance only: verify own preserved seals, native tool and source identities."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent.parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
def h(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
old=[('research/rmaf/algorithm/verification/good-pair-consumer-2026-10-15/sol-review-CONFIRMED-v1',213,'30c9c5d829cda6999fd4c2ba40eb34256996252690952b63f8289a9efaa7ce46','86ed5a198689f751072e6b479a67473aaf8c55292500812c6e76c49d39a7218f'),('research/rmaf/algorithm/verification/good-pair-consumer-2026-10-15/sol-preparation-READY-v1',109,'ccace5653dd25e1844e8477ef09c6b0b3e5f31ad2d555392962cb9dc97bf9d34b3a','e4cd9e45d7f97465b494b5fb0e6ad6398a0582a28c4612e03c2bce438c024570'),('research/rmaf/algorithm/pair_case/cheap_high/x0/sol-handoff-v1',36,'4bf3403507f3ce517b1e3010de4c581fbd202afdf579f7c77300b1dc26562d3b','a6f04044562895cbd8343b64b8e507d8e3bc633cd8f1df03bc3fd0eb8942f216')]
# The READY hash is read literally from the earlier parent release; no source content is imported.
old[1]=(old[1][0],109,'ccace5653dd25e1844e8477ef09c6b0b3e5f31ad2d555392cb9dc97bf9d34b3a',old[1][3])
rows=[]
for rel,n,msha,asha in old:
 d=ROOT/rel;m=d/'MANIFEST.json';manifest=json.loads(m.read_text());entries=manifest['entries'];bad=[]
 for e in entries:
  z=d/e['path']
  if not z.is_file() or h(z)!=e['sha256'] or z.stat().st_size!=e['bytes']:bad.append(e['path'])
 a=Path(str(d)+'.tar.gz');row={'snapshot':rel,'expected_entries':n,'checked_entries':len(entries),'bad_entries':bad,'manifest_sha256':h(m),'expected_manifest_sha256':msha,'archive_sha256':h(a),'expected_archive_sha256':asha}
 row['all_pass']=len(entries)==n and not bad and row['manifest_sha256']==msha and row['archive_sha256']==asha;rows.append(row)
TC=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0';lean=TC/'bin/lean'
files=[lean,TC/'lib/lean/libleanshared.dylib',ROOT/'bootloops-python',P.parent/'TARGET-v1.md',P/'instrument/x0_evaluator_reused.py']
for rel in ['Lean/Util/CollectAxioms.lean','Lean/Environment.lean','Lean/PrivateName.lean','Lean/Data/SMap.lean','Lean/MonadEnv.lean','Lean/Parser/Module.lean']:files.append(TC/'src/lean'/rel)
meta=[{'path':str(f),'bytes':f.stat().st_size,'sha256':h(f)} for f in files if f.is_file()]
out={'phase':'PRE-CANDIDATE ONLY','preservation':rows,'all_pass':all(r['all_pass']for r in rows),'native_lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'file_identities':meta,'candidate_contact':False,'candidate_compilation':False,'replication_increment':0,'all_three_main_milestones':'OPEN','shared_Lean_Std_dependency_boundary':'Native installed library binaries are used; not rebuilt or reviewed in this preparation. No scientific CoreGraph dependency was compiled or loaded.'}
(P/'preservation-provenance-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'all_pass':out['all_pass'],'preserved_entries':[r['checked_entries'] for r in rows],'native_lean_version':out['native_lean_version']},indent=2))
raise SystemExit(0 if out['all_pass'] else 1)
