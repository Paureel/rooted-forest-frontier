#!/usr/bin/env python3
# One-shot nonauthor replay: existing tools index has no Lean/graph review driver;
# wrapper reuses pinned Lean and independently audits environment declarations.
from pathlib import Path
import hashlib, json, re, shutil, subprocess, time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
D=ROOT/'research/rmaf/algorithm/universal233/review-core'
SRC=D.parent/'core/replay/20261015T063857Z'
B=D/'rebuild'
B.mkdir(exist_ok=True)
mods=['RMAF','CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants']
false=['FalseExactPartition','FalseOneBranch','FalseRootCut']
hashes={}
for n in mods+false:
    data=(SRC/(n+'.lean')).read_bytes(); (B/(n+'.lean')).write_bytes(data)
    hashes[n+'.lean']=hashlib.sha256(data).hexdigest()
(B/'lean-toolchain').write_bytes((SRC/'lean-toolchain').read_bytes())
(D/'frozen-input-sha256.json').write_text(json.dumps(hashes,indent=2)+'\n')
scan={n:re.findall(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b', re.sub(r'/\*[\s\S]*?\*/|--[^\n]*', '', (B/(n+'.lean')).read_text()), re.M) for n in mods}
assert not any(scan.values()),scan
(D/'prohibited-proof-scan.json').write_text(json.dumps(scan,indent=2)+'\n')
# No cached object files are copied or reused from author delivery.
for f in B.glob('*.olean'): f.unlink()
def run(n,expected=0,build=False):
    cmd=[str(ROOT/'bootloops-lean')]
    if build: cmd+=['-o',n+'.olean']
    cmd+=[n+'.lean']
    env=__import__('os').environ.copy(); env['LEAN_PATH']=str(B)
    start=time.monotonic(); p=subprocess.run(cmd,cwd=B,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=90)
    (B/(n+'.log')).write_text(p.stdout)
    row={'module':n,'returncode':p.returncode,'seconds':round(time.monotonic()-start,4),'command':cmd,'source_sha256':hashlib.sha256((B/(n+'.lean')).read_bytes()).hexdigest()}
    times.append(row)
    (D/'lean-phase-timings.json').write_text(json.dumps(times,indent=2)+'\n')
    if expected==0: assert p.returncode==0,(n,p.stdout)
    else: assert p.returncode!=0 and 'decide' in p.stdout and 'false' in p.stdout.lower(),(n,p.stdout)
    return p.stdout
prefix='''import CoreInvariants\nimport CherryCoarsening\nimport Lean\nopen Lean Elab Command\n'''
body='''run_cmd do
  let env ← getEnv
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter (fun n => (`Universal233).isPrefixOf n || (`RMAF).isPrefixOf n)).eraseDups
  let ns := ns.mergeSort Name.quickLt
  for n in ns do logInfo m!"DECL|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"AUDIT|{n}|{axs.toList}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''
(B/'FreshAudit.lean').write_text(prefix+body)
(B/'AuditPlant.lean').write_text(prefix+'namespace Universal233.Plants\naxiom stolen : False\nend Universal233.Plants\n'+body)
(B/'CleanTwin.lean').write_text('import CoreProgram\nexample : True := by decide\n')
times=[]
# Compiler trivial known truth pilot first, before actual module replay.
(B/'Pilot.lean').write_text('import Std\nexample : 2 + 2 = 4 := by decide\n')
run('Pilot')
for n in mods: run(n,build=True)
run('CleanTwin')
for n in false: run(n,expected=1)
log=run('FreshAudit')
def audit_parse(s):
    decl=re.findall(r'^DECL\|(.+)$',s,re.M)
    audit=re.findall(r'^AUDIT\|([^|]+)\|(.+)$',s,re.M)
    assert decl and len(decl)==len(set(decl))
    assert set(decl)=={x[0] for x in audit} and len(decl)==len(audit),'missing/duplicate audit records'
    return {'total':len(decl),'core':sum(x.startswith('Universal233.') for x in decl),'shared_spec_dependency':sum(x.startswith('RMAF.') for x in decl)}
counts=audit_parse(log)
try: audit_parse(re.sub(r'^AUDIT\|[^\n]+\n','',log,count=1,flags=re.M))
except AssertionError: missing_caught=True
else: raise AssertionError('missing-record plant survived')
# Custom axiom plant is expected to fail by our exact rejection marker, not syntax.
env=__import__('os').environ.copy(); env['LEAN_PATH']=str(B)
p=subprocess.run([str(ROOT/'bootloops-lean'),'AuditPlant.lean'],cwd=B,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=90)
(B/'AuditPlant.log').write_text(p.stdout)
assert p.returncode!=0 and 'REJECT_CUSTOM_AXIOM' in p.stdout and 'stolen' in p.stdout,p.stdout
summary={'status':'CONFIRMED','counts':counts,'false_controls_rejected':false,'clean_twin':'compiled','custom_axiom_plant':'caught','missing_record_plant':'caught','timings':times}
(D/'lean-replay-verdict.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
