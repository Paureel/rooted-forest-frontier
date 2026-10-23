#!/usr/bin/env python3
# One-shot source-bound replay for binary E; deliberately not a toolkit engine.
from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, time

ROOT = Path(__file__).resolve().parents[6]
ARM = Path(__file__).resolve().parent
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT = ROOT / 'research/rmaf/results' / ('algorithm-pair-case-exchange-' + STAMP)
SRC, OLEAN = OUT/'source', OUT/'olean'
SRC.mkdir(parents=True); OLEAN.mkdir()
MODULES = ['RMAF','Geometry','Bridge','Restriction','Cluster','Descendant','Forest','Surgery','Count','Parents','Exchange','Controls']
ORIGINALS = {'RMAF': ROOT/'research/rmaf/lean/RMAF.lean', 'Geometry': ROOT/'research/rmaf/algorithm/universal233/geometry/Geometry.lean', 'Bridge': ROOT/'research/rmaf/algorithm/universal233/geometry/Bridge.lean'}
manifest = {'status':'RUNNING','utc':STAMP,'files':{},'runs':[],'claims':'AUTHOR-LEAN only if all gates pass; semantic/consumer review pending'}
def save():
    (OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
def copy(path, target):
    shutil.copyfile(path,target)
    manifest['files'][str(target.relative_to(OUT))]={'origin':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
for m in MODULES: copy(ORIGINALS.get(m, ARM/(m+'.lean')), SRC/(m+'.lean'))
copy(ARM/'Audit.lean',SRC/'Audit.lean')
copy(ARM/'CONTROL-PIN.md',OUT/'CONTROL-PIN.md')
copy(Path(__file__),OUT/'replay.py')
for f in sorted((ARM/'controls').glob('*.lean')): copy(f,SRC/f.name)
# Control audits use the identical audit body; only the imported/inventoried module changes.
audit = (SRC/'Audit.lean').read_text()
for stem in ['CleanTwin','AxiomPlant']:
    text = audit.replace('import Controls','import Controls\nimport '+stem).replace('`Exchange,`Controls]','`Exchange,`Controls,`'+stem+']')
    (SRC/(stem+'Audit.lean')).write_text(text)
    manifest['files']['source/'+stem+'Audit.lean']={'origin':'derived from exact Audit.lean; added import and origin inventory '+stem,'sha256':hashlib.sha256(text.encode()).hexdigest()}
save()
env=os.environ.copy(); env['LEAN_PATH']=str(OLEAN)
def run(name, expect_ok=True, semantic_false=False, axiom_reject=False):
    log=OUT/(name+'.log')
    args=[str(ROOT/'bootloops-lean')]
    if expect_ok and name not in ['Audit','CleanTwinAudit','AxiomPlantAudit']: args += ['-o',str(OLEAN/(name+'.olean'))]
    args += [str(SRC/(name+'.lean'))]
    start=time.monotonic()
    p=subprocess.run(args,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
    log.write_text(p.stdout)
    row={'module':name,'returncode':p.returncode,'seconds':round(time.monotonic()-start,6),'log':log.name,'expected':'compile' if expect_ok else 'explicit semantic false' if semantic_false else 'custom axiom rejected'}
    manifest['runs'].append(row); save()
    if expect_ok: assert p.returncode==0, row
    if semantic_false:
        assert p.returncode!=0 and 'Tactic `decide` proved that the proposition' in p.stdout and 'is false' in p.stdout, row
    if axiom_reject:
        assert p.returncode!=0 and 'BinaryExchange.PlantedAudit.unusedCustom' in p.stdout and '_private.' in p.stdout and 'Originating-module axiom/unsafe audit rejected' in p.stdout, row
    return row
try:
    # Measured pilot before the whole chain; same compiler/source configuration.
    run('RMAF')
    for m in MODULES[1:]: run(m)
    run('Audit')
    for m in ['FalseWholeB','FalseWholeBCut','FalseNoCluster','FalseBoundary','FalseAbsent']:
        run(m,expect_ok=False,semantic_false=True)
    run('CleanTwin'); run('CleanTwinAudit')
    run('AxiomPlant'); run('AxiomPlantAudit',expect_ok=False,axiom_reject=True)
    # Ban admission/native proof mechanisms from scientific candidate modules.
    import re
    for m in MODULES:
        text=(SRC/(m+'.lean')).read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)),m
    counts={}
    for line in (OUT/'Audit.log').read_text().splitlines():
        if line.startswith('MODULE_COUNT|'):
            _,m,n=line.split('|'); counts[m]=int(n)
    assert set(counts)==set(MODULES) and all(counts.values()),counts
    manifest['origin_declaration_counts']=counts
    manifest['origin_declarations_total']=sum(counts.values())
    manifest['status']='AUTHOR-LEAN; fresh nonauthor semantic/consumer review pending'
except Exception as exc:
    manifest['status']='FAILED'; manifest['error']=repr(exc); save(); print(OUT); raise
save()
print(json.dumps({'result':str(OUT),'status':manifest['status'],'declarations':manifest['origin_declarations_total'],'runs':len(manifest['runs'])},indent=2))
