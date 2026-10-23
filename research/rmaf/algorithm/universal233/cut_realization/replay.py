#!/usr/bin/env python3
"""One-shot source-bound original-cut proof replay, extending frozen imports.

All proof modules are copied and rebuilt in isolation. Audits inspect every
module-origin declaration, including generated/private declarations. This is an
author kernel replay; independent hostile/nonauthor review remains separate.
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
FROZEN = [('RMAF', ROOT / 'research/rmaf/lean/RMAF.lean')]
FROZEN += [(n, BASE/'geometry'/(n+'.lean')) for n in ('Geometry','Bridge','Composition')]
FROZEN += [(n, BASE/'core'/(n+'.lean')) for n in ('CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants')]
FROZEN += [(n, BASE/'integration'/(n+'.lean')) for n in (
    'SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','CutRecords')]
LOCAL_NAMES = ['OriginalGraph','Display','Regions','History','Realization','OwnerCover','Coverage',
               'InitialCoverage','Cost','ValidPartition','CutControls']
SPECS = FROZEN + [(n,HERE/(n+'.lean')) for n in LOCAL_NAMES]
ALLOWED = {'Classical.choice','propext','Quot.sound'}
NEGATIVE = HERE/'FalseCutControls.lean'
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
OUT = HERE/'replay'/STAMP
OUT.mkdir(parents=True, exist_ok=False)
(HERE/'LATEST-REPLAY.txt').write_text(str(OUT)+'\n')
RESULT = ROOT/'results'/('algorithm-universal233-cut-realization-author-'+STAMP+'.json')
ENV = dict(os.environ, LEAN_PATH=str(OUT))
record = {'grade':'AUTHOR KERNEL REPLAY; fresh independent review pending',
          'source_core_kernel_checked':False, 'full_algorithm_proved':False,
          'raw_mass_proved':False,'polynomial_prefix_work_proved':False,
          'receipt':str(OUT.relative_to(ROOT)), 'builds':[], 'hashes':{}}


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def clean(s):
    s = re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group().count('\n'),s,flags=re.S)
    return re.sub(r'--[^\n]*','',s)


def save():
    (OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
    RESULT.write_text(json.dumps(record,indent=2)+'\n')


def check_pins(pins):
    for rel, expected in pins.items():
        if digest(ROOT/rel) != expected:
            raise RuntimeError('SOURCE_PIN_MISMATCH|'+rel)


inputs = [p for _,p in SPECS]+[NEGATIVE,Path(__file__),HERE/'lean-toolchain',ROOT/'bootloops-lean',ROOT/'bootloops-python']
for p in inputs:
    record['hashes'][str(p.relative_to(ROOT))] = digest(p)
    if p.suffix == '.lean':
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean(p.read_text())):
            raise RuntimeError('FORBIDDEN_PROOF_ESCAPE|'+str(p))
        (OUT/p.name).write_bytes(p.read_bytes())
(OUT/'lean-toolchain').write_bytes((HERE/'lean-toolchain').read_bytes())
save()


def run(name, build=False, timeout=30):
    args = [str(ROOT/'bootloops-lean')]
    if build:
        args += ['-o',str(OUT/(name+'.olean'))]
    args += [str(OUT/(name+'.lean'))]
    start = time.monotonic()
    p = subprocess.run(args,cwd=OUT,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=timeout)
    (OUT/(name+'.log')).write_text(p.stdout)
    record['builds'].append({'module':name,'exit':p.returncode,'seconds':time.monotonic()-start})
    save()
    return p


for n,_ in SPECS:
    p = run(n,True)
    if p.returncode or re.search(r'error:|sorryAx|declaration uses .sorry.',p.stdout):
        raise SystemExit('FAIL_POSITIVE_BUILD|'+n)

modules = ', '.join('`'+n for n,_ in SPECS)
audit = '''import CutControls
import Lean
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
p = run('ModuleInventory')
if p.returncode:
    raise SystemExit('FAIL_MODULE_ORIGIN_AUDIT')


def parse_audit(s):
    m = re.findall(r'^MODULE\|([^|]+)\|(.+)$',s,re.M)
    a = re.findall(r'^MODAUDIT\|([^|]+)\|\[(.*?)\]$',s,re.M)
    if not m or len(m)!=len(a) or len(m)!=len(set(m)) or {n for _,n in m}!={n for n,_ in a}:
        raise RuntimeError('MISSING_OR_DUPLICATE_AUDIT_RECORD')
    axs = {z.strip() for _,v in a for z in v.split(',') if z.strip()}
    if not axs <= ALLOWED:
        raise RuntimeError('UNAPPROVED_AXIOM_SET|'+str(axs))
    return m,a,axs


m,a,axs = parse_audit(p.stdout)
if {mod for mod,_ in m} != {n for n,_ in SPECS}:
    raise SystemExit('FAIL_MODULE_ORIGIN_SET')
try:
    parse_audit(re.sub(r'^MODAUDIT\|[^\n]+\n','',p.stdout,count=1,flags=re.M))
except RuntimeError:
    missing_plant = 'CAUGHT'
else:
    raise SystemExit('FAIL_MISSING_RECORD_PLANT_SURVIVED')

# Deliberate custom axiom outside the proof namespace tests module-origin coverage.
(OUT/'AuditPlant.lean').write_text('namespace OutsideProofNamespace\naxiom borrowed : False\nend OutsideProofNamespace\n')
p = run('AuditPlant',True)
if p.returncode:
    raise SystemExit('FAIL_PLANT_MODULE_BUILD')
(OUT/'ModulePlantAudit.lean').write_text('import AuditPlant\n'+audit.replace('`CutControls]','`CutControls, `AuditPlant]'))
p = run('ModulePlantAudit')
if p.returncode==0 or 'REJECT_CUSTOM_AXIOM|OutsideProofNamespace.borrowed|OutsideProofNamespace.borrowed' not in p.stdout:
    raise SystemExit('FAIL_CUSTOM_AXIOM_PLANT_SURVIVED')

bad_pins = dict(record['hashes'])
first = next(iter(bad_pins))
bad_pins[first] = '0'*64
try:
    check_pins(bad_pins)
except RuntimeError:
    pin_plant = 'CAUGHT'
else:
    raise SystemExit('FAIL_SOURCE_PIN_PLANT_SURVIVED')

p = run('FalseCutControls')
if p.returncode==0 or p.stdout.count('is false')!=4:
    raise SystemExit('FAIL_FOUR_FALSE_CONTROLS_NOT_REJECTED')

keys = ['History.continuation_realizes','History.continuation_components','generate_original_realization',
        'generate_refinement_coverage','generate_realized_color_cost','generate_cost_bound',
        'generate_partition_check','checked_source_core']
(OUT/'Interfaces.lean').write_text('import CutControls\n'+''.join('#check Universal233.CutRealization.'+k+'\n' for k in keys))
p = run('Interfaces')
if p.returncode:
    raise SystemExit('FAIL_INTERFACE_ELABORATION')
check_pins(record['hashes'])
record.update({'source_core_kernel_checked':True,'positive_source_builds':len(SPECS),
    'local_source_modules':LOCAL_NAMES,
    'module_origin_declarations':len(m),
    'module_counts':{k:sum(mod==k for mod,_ in m) for k in sorted({mod for mod,_ in m})},
    'axiom_union_observed':sorted(axs),
    'private_generated_included':True,
    'missing_record_plant':missing_plant,'source_pin_plant':pin_plant,
    'foreign_custom_axiom_plant':'CAUGHT','false_controls_rejected':4,
    'positive_fixture_theorems':[n for n in re.findall(r'^theorem (\w+)',(HERE/'CutControls.lean').read_text(),re.M)
      if n not in {'regionCheck_correct','leafPairs_correct','leafLabels_correct'}],
    'meaning':'Exact original-component soundness, finite-budget monochromatic source refinement coverage and realized cut bounds kernel checked. Author replay only; fresh independent review, raw mass, polynomial per-prefix work and full faster algorithm remain separate.'})
record['module_origin_inventory']=[{'module':mod,'name':n} for mod,n in m]
record['axioms_by_declaration']={n:[z.strip() for z in v.split(',') if z.strip()] for n,v in a}
save()
(OUT/'SHA256SUMS.json').write_text(json.dumps(record['hashes'],indent=2)+'\n')
verdict = f"PASS: {len(SPECS)} isolated source builds; {len(m)} full module-origin declaration audits; {len(record['positive_fixture_theorems'])} positive fixture theorems; 4 rejected false controls; 3 caught audit/pin plants"
(OUT/'VERDICT.txt').write_text(verdict+'\nAUTHOR KERNEL REPLAY; independent review pending; mass/work/full algorithm OPEN\n')
print(verdict)
print('Receipt:',OUT)
print('Result:',RESULT)
