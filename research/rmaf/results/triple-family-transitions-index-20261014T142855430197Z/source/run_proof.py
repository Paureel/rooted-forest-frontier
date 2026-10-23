#!/usr/bin/env python3
"""One-shot isolated rebuild and explicit controls for this proof route.
Run via ./bootloops-python; imports are copied only from approved old sources.
Writes timestamped snapshots, per-command logs, hashes, and exact control counts.
A pass requires all compile stages, actual false-proposition diagnostics, clean
counterparts, all frozen positive enumerations, and standard axiom reports.
"""
import datetime, hashlib, json, os, pathlib, re, shutil, subprocess, time
ROOT = pathlib.Path(__file__).resolve().parents[6]
OWN = pathlib.Path(__file__).resolve().parent
STAMP = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
OUT = ROOT / 'research/rmaf/results' / ('triple-family-transitions-index-' + STAMP)
SRC = OUT / 'source'
SRC.mkdir(parents=True)
files = [ROOT/'research/rmaf/triple_dp/TripleDP.lean', ROOT/'research/rmaf/triple_dp/ConnectedRegions.lean', ROOT/'research/rmaf/triple_dp/family/cost_route/FamilyAssembly.lean', OWN/'IndexRoute.lean']
records = files+[OWN/'controls.json', OWN/'run_proof.py', OWN/'check_controls.py']
for file in records:
    shutil.copyfile(file, SRC/file.name)
manifest = {str(file.relative_to(ROOT)): hashlib.sha256(file.read_bytes()).hexdigest() for file in records}
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
env = dict(os.environ, ELAN_HOME=str(ROOT/'.runtime/elan'), LEAN_PATH=str(SRC))
version = subprocess.run([str(ROOT/'bootloops-lean'),'--version'], cwd=SRC, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
(OUT/'version.log').write_text(version.stdout)
rows = []
positive_count = 0

def run(name, compile_output=False, false_statement=None):
    command=[str(ROOT/'bootloops-lean')]
    if compile_output:
        command += ['-o',name+'.olean']
    command += [name+'.lean']
    start=time.monotonic()
    result=subprocess.run(command,cwd=SRC,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
    (OUT/(name+'.log')).write_text(result.stdout)
    expected_pass = result.returncode == 0
    if false_statement is not None:
        expected_pass = (result.returncode != 0 and
            'Tactic `decide` proved that the proposition\n  '+false_statement+'\nis false' in result.stdout and
            result.stdout.count('error:') == 1)
    rows.append(dict(name=name,command=command,returncode=result.returncode,seconds=time.monotonic()-start,expected_pass=expected_pass))
    return expected_pass

for file in files:
    if not run(file.stem,compile_output=True):
        break
if len(rows) == 4 and rows[-1]['expected_pass']:
    tests = [('FalseCount','singletonEnums.length = 2'), ('FalseCharge','singletonClosed.length = 1'), ('FalseCollision','collisionLeft = collisionRight'), ('CleanTwins','singletonEnums.length = 1 ∧ singletonClosed.length = 0 ∧ collisionLeft ≠ collisionRight')]
    for name, statement in tests:
        (SRC/(name+'.lean')).write_text('import IndexRoute\nopen TripleDP.CostRoute.IndexRoute\nexample : '+statement+' := by decide\n')
        run(name,false_statement=None if name=='CleanTwins' else statement)
    spec=json.loads((OWN/'controls.json').read_text())
    positive_count=len(spec['positive'])
    lines=['import IndexRoute','open TripleDP.CostRoute.IndexRoute']
    for f in spec['positive']:
        args=' '.join(['('+json.dumps(f['left'])+' : List String)', '('+json.dumps(f['right'])+' : List String)', json.dumps(f['left_boundary']),json.dumps(f['right_boundary'])])
        expected=[]
        for item in f['expected']:
            if item=='M':
                expected.append('Joined.boundary')
            else:
                constructor='left' if item.startswith('L:') else 'right'
                expected.append('Joined.'+constructor+' ⟨'+json.dumps(item[2:])+', by decide⟩')
        lines+=['-- '+f['id'], 'example : enumeration '+args+' = ['+', '.join(expected)+'] := by decide', 'example : (enumeration '+args+').length = '+str(f['blocks'])+' ∧ (closedEnumeration '+args+').length = '+str(f['closed'])+' := by decide']
    (SRC/'FrozenPositives.lean').write_text('\n'.join(lines)+'\n')
    run('FrozenPositives')

text=(SRC/'IndexRoute.lean').read_text()
log=(OUT/'IndexRoute.log').read_text() if (OUT/'IndexRoute.log').exists() else ''
expected_names=re.findall(r'^#print axioms (\w+)$',text,re.MULTILINE)
reported=re.findall(r"'TripleDP.CostRoute.IndexRoute.(\w+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
axioms={a.strip() for _, group in reported for a in group.split(',') if a.strip()}
forbidden=re.findall(r'\b(?:sorry|admit|native_decide|unsafe)\b|^\s*axiom\s+',text,re.MULTILINE)
audit=dict(expected_declarations=len(expected_names),reported_declarations=len(reported),names_complete=sorted(expected_names)==sorted(name for name,_ in reported),axioms=sorted(axioms),source_forbidden_tokens=forbidden)
audit['passed']=audit['names_complete'] and axioms <= {'propext','Quot.sound','Classical.choice'} and not forbidden
(OUT/'axiom-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
(OUT/'generated-manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in SRC.glob('*.lean')},indent=2)+'\n')
(OUT/'results.json').write_text(json.dumps(rows, indent=2)+'\n')
passed=(version.returncode==0 and 'version 4.35.0' in version.stdout and len(rows)==9 and positive_count==5 and all(r['expected_pass'] for r in rows) and audit['passed'])
summary=dict(receipt=str(OUT.relative_to(ROOT)),passed=passed,compiled_modules=sum(r['returncode']==0 and r['name'] in {p.stem for p in files} for r in rows),false_lean_controls=sum(r['name'].startswith('False') and r['expected_pass'] for r in rows),clean_twin_propositions=3 if any(r['name']=='CleanTwins' and r['expected_pass'] for r in rows) else 0,frozen_positive_cases=positive_count if any(r['name']=='FrozenPositives' and r['expected_pass'] for r in rows) else 0,axiom_audit=audit,total_seconds=sum(r['seconds'] for r in rows))
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
raise SystemExit(0 if passed else 1)
