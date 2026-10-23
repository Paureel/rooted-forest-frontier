#!/usr/bin/env python3
"""One-shot source-bound hard-parent proof replay.

Uses unchanged frozen RMAF/graph modules, rebuilds all local proof sources in a
new receipt, audits every module-origin declaration including generated/private
names, executes positive/negative controls, and freezes the completed receipt.
This author replay does not claim fresh nonauthor verification.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = HERE.parent
FROZEN = [('RMAF', ROOT/'research/rmaf/lean/RMAF.lean')]
FROZEN += [(n, BASE/'geometry'/(n+'.lean')) for n in ('Geometry','Bridge','Composition')]
FROZEN += [(n, BASE/'core'/(n+'.lean')) for n in ('CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants')]
FROZEN += [(n, BASE/'integration'/(n+'.lean')) for n in (
    'SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords')]
FROZEN += [('OriginalGraph', BASE/'cut_realization/OriginalGraph.lean')]
LOCAL_NAMES = ['Executable','Endpoint','Restriction','PendantExclusion','Refinement','Components','Safety','Controls']
SPECS = FROZEN + [(n,HERE/(n+'.lean')) for n in LOCAL_NAMES]
ALLOWED = {'Classical.choice','propext','Quot.sound'}
NEGATIVE = HERE/'FalseControls.lean'
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT = ROOT/'results'/('algorithm-universal233-hard-refinement-'+STAMP)
OUT.mkdir(parents=True,exist_ok=False)
(HERE/'LATEST-RECEIPT.txt').write_text(str(OUT)+'\n')
ENV = dict(os.environ,LEAN_PATH=str(OUT))
MANIFEST = BASE/'cut_realization/CUT-REALIZATION-MANIFEST-v1.json'
FROZEN_PINS = json.loads(MANIFEST.read_text())['exact_source_import_pins']
record = {'status':'AUTHOR KERNEL REPLAY; fresh hostile/nonauthor verification pending',
    'hard_parent_source_safety_kernel_checked':False,'full_algorithm_proved':False,
    'main_milestones':'ALL THREE OPEN','receipt':str(OUT.relative_to(ROOT)),
    'builds':[],'hashes':{},'frozen_manifest':str(MANIFEST.relative_to(ROOT))}

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(): (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
def clean(s):
    s=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
    return re.sub(r'--[^\n]*','',s)
def check_pins(pins):
    for rel,expected in pins.items():
        if digest(ROOT/rel)!=expected: raise RuntimeError('SOURCE_PIN_MISMATCH|'+rel)

# Input pins are checked against the retained frozen manifest before copying.
for n,p in FROZEN:
    rel=str(p.relative_to(ROOT))
    if rel not in FROZEN_PINS or digest(p)!=FROZEN_PINS[rel]:
        raise SystemExit('FAIL_FROZEN_SOURCE_PIN|'+rel)

inputs=[p for _,p in SPECS]+[NEGATIVE,Path(__file__),HERE/'lean-toolchain',
    ROOT/'bootloops-lean',ROOT/'bootloops-python',MANIFEST,
    BASE/'assembly/HARD-PARENT-REFINEMENT-TARGET-v1.md',
    ROOT/'research/rmaf/sources/baseline/split-or-decompose-v2.txt',
    HERE/'CONTROLS-PIN.md',HERE/'RESULT.md',HERE/'SOURCE-LEDGER.md',HERE/'INTERFACE.md']
for p in inputs:
    record['hashes'][str(p.relative_to(ROOT))]=digest(p)
    if p.suffix=='.lean':
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(p.read_text())):
            raise SystemExit('FORBIDDEN_PROOF_ESCAPE|'+str(p))
        (OUT/p.name).write_bytes(p.read_bytes())
(OUT/'lean-toolchain').write_bytes((HERE/'lean-toolchain').read_bytes())
for n in ('CONTROLS-PIN.md','RESULT.md','SOURCE-LEDGER.md','INTERFACE.md'):
    (OUT/n).write_bytes((HERE/n).read_bytes())
save()

def run(name,build=False,timeout=30):
    args=[str(ROOT/'bootloops-lean')]
    if build: args+=['-o',str(OUT/(name+'.olean'))]
    args+=[str(OUT/(name+'.lean'))]
    start=time.monotonic()
    p=subprocess.run(args,cwd=OUT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
    (OUT/(name+'.log')).write_text(p.stdout)
    record['builds'].append({'module':name,'exit':p.returncode,'seconds':time.monotonic()-start})
    save()
    return p

start=time.monotonic()
for n,_ in SPECS:
    p=run(n,True)
    if p.returncode or re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout):
        raise SystemExit('FAIL_POSITIVE_BUILD|'+n)

modules=', '.join('`'+n for n,_ in SPECS)
imports=''.join('import '+n+'\n' for n,_ in SPECS)
audit=imports+'''import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [MODULES]
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{axs.toList}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
'''.replace('MODULES',modules)
(OUT/'ModuleInventory.lean').write_text(audit)
p=run('ModuleInventory')
if p.returncode: raise SystemExit('FAIL_MODULE_ORIGIN_AUDIT')

def parse_audit(s):
    m=re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M)
    a=re.findall(r'^MODAUDIT\|([^|]+)\|\[(.*?)\]$',s,re.M)
    if not m or len(m)!=len(a) or len(m)!=len(set(m)) or {n for _,n in m}!={n for n,_ in a}:
        raise RuntimeError('MISSING_OR_DUPLICATE_AUDIT_RECORD')
    axs={z.strip() for _,v in a for z in v.split(',') if z.strip()}
    if not axs<=ALLOWED: raise RuntimeError('UNAPPROVED_AXIOM_SET|'+str(axs))
    return m,a,axs
m,a,axs=parse_audit(p.stdout)
if {mod for mod,_ in m}!={n for n,_ in SPECS}: raise SystemExit('FAIL_MODULE_ORIGIN_SET')
if not any(mod=='Controls' and '_private' in n and 'internal_control' in n for mod,n in m):
    raise SystemExit('FAIL_PRIVATE_DECLARATION_NOT_INVENTORIED')
try: parse_audit(re.sub(r'^MODAUDIT\|[^\n]+\n','',p.stdout,count=1,flags=re.M))
except RuntimeError: missing='CAUGHT'
else: raise SystemExit('FAIL_MISSING_RECORD_PLANT_SURVIVED')

# Private custom axiom in a foreign namespace: source-level namespace scans
# cannot replace the complete declaration-origin/recursive axiom audit.
(OUT/'AuditPlant.lean').write_text('namespace OutsideProofNamespace\nprivate axiom concealed : False\nprivate theorem touched : False := concealed\nend OutsideProofNamespace\n')
p=run('AuditPlant',True)
if p.returncode: raise SystemExit('FAIL_PLANT_MODULE_BUILD')
planted='import AuditPlant\n'+audit.replace('`Controls]','`Controls, `AuditPlant]')
(OUT/'ModulePlantAudit.lean').write_text(planted)
p=run('ModulePlantAudit')
if p.returncode==0 or 'REJECT_CUSTOM_AXIOM|' not in p.stdout or 'concealed' not in p.stdout:
    raise SystemExit('FAIL_HIDDEN_CUSTOM_AXIOM_PLANT_SURVIVED')

bad=dict(record['hashes']); bad[next(iter(bad))]='0'*64
try: check_pins(bad)
except RuntimeError: pinplant='CAUGHT'
else: raise SystemExit('FAIL_SOURCE_PIN_PLANT_SURVIVED')
p=run('FalseControls')
if p.returncode==0 or p.stdout.count('is false')!=5:
    raise SystemExit('FAIL_FIVE_FALSE_PROPOSITIONS_NOT_REJECTED')

keys=['actual_hard2_source_safety','actual_hard2_named_safety','actual_hard2_unordered_safety',
      'original_pendant_spec','literalOriginalThree_construct','literalThree_partition',
      'hard2_endpoints_in_root','original_common_block_excluded','actual_cherry_endpoint_alternative']
(OUT/'Interfaces.lean').write_text('import Controls\n'+''.join('#check Universal233.HardParent.'+k+'\n' for k in keys))
p=run('Interfaces')
if p.returncode: raise SystemExit('FAIL_INTERFACE_ELABORATION')
check_pins(record['hashes'])
record.update({'hard_parent_source_safety_kernel_checked':True,
    'positive_source_builds':len(SPECS),'local_modules':LOCAL_NAMES,
    'module_origin_declarations':len(m),'private_generated_included':True,
    'module_counts':{k:sum(mod==k for mod,_ in m) for k in sorted({mod for mod,_ in m})},
    'axiom_union_observed':sorted(axs),'missing_record_plant':missing,
    'source_pin_plant':pinplant,'hidden_foreign_private_custom_axiom_plant':'CAUGHT',
    'false_propositions_rejected':5,'seconds_measured':time.monotonic()-start,
    'positive_controls':[n for source in ('Executable','Controls') for n in re.findall(r'^theorem (control_\w+)',(HERE/(source+'.lean')).read_text(),re.M)],
    'module_origin_inventory':[{'module':mod,'name':n} for mod,n in m],
    'axioms_by_declaration':{n:[z.strip() for z in v.split(',') if z.strip()] for n,v in a},
    'meaning':'Original hard2 cherry branch cover with literal original residual components and no leafless regions, author kernel replay only. Fresh hostile/nonauthor acceptance and every global algorithm milestone remain separate.'})
save()
(OUT/'SOURCE-PINS.json').write_text(json.dumps(record['hashes'],indent=2)+'\n')
verdict=f'PASS: {len(SPECS)} isolated source builds; {len(m)} complete module-origin audits; {len(record["positive_controls"])} positive controls; 5 rejected false propositions; 3 caught audit/pin plants'
(OUT/'VERDICT.txt').write_text(verdict+'\nAUTHOR KERNEL REPLAY; fresh hostile/nonauthor verification pending; all three main algorithm milestones OPEN\n')
files={p.name:{'sha256':digest(p),'bytes':p.stat().st_size} for p in sorted(OUT.iterdir()) if p.is_file()}
(OUT/'RECEIPT-FILES.json').write_text(json.dumps(files,indent=2)+'\n')
for p in OUT.iterdir():
    if p.is_file(): p.chmod(0o444)
OUT.chmod(0o555)
print(verdict)
print('Frozen receipt:',OUT)
