#!/usr/bin/env python3
"""One-shot final-review source-isolated Lean rebuild. No project checker reuse.
Reads author manifest as data, verifies all pins and logs, and rebuilds bytes in
its own module directory with LEAN_PATH pointing only there. Emits incremental
receipt; nonzero semantic controls require an explicit decide-false diagnostic.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
ROOT=Path(__file__).resolve().parents[5]
HERE=Path(__file__).resolve().parent
AUTHOR=ROOT/'research/rmaf/bridge_review/degree_two/replay/20261014T145838Z/receipt.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(AUTHOR)=='7b6cea342c8b72c04907643d7075c5bdd36758950e83d0e10af72732aef3fa43'
data=json.loads(AUTHOR.read_text())
BUILD=HERE/'isolated'; BUILD.mkdir(exist_ok=True)
LOG=HERE/'logs'; LOG.mkdir(exist_ok=True)
rows=[]; pins=[]
def save():
 (HERE/'rebuild-receipt.json').write_text(json.dumps(dict(status='running',author_sha256=sha(AUTHOR),pins=pins,builds=rows),indent=2)+'\n')
for p,h in data['source_pins'].items():
 s=ROOT/p
 assert sha(s)==h,p
 pins.append(dict(path=p,sha256=h))
for r in data['builds_and_controls']:
 assert sha(ROOT/r['source'])==r['source_sha256'],r['source']
 assert sha(ROOT/r['log'])==r['log_sha256'],r['log']
 assert r['exit_code']==r['expected_exit'],r['name']
 if r.get('explicit_false'): assert 'decide' in (ROOT/r['log']).read_text() and 'false' in (ROOT/r['log']).read_text().lower(),r['name']
assert sha(ROOT/data['script'])==data['script_sha256']
env=os.environ.copy(); env['LEAN_PATH']=str(BUILD)

def run(name, source, expected=0, explicit=False, output=True):
 dest=BUILD/source.name
 dest.write_bytes(source.read_bytes())
 cmd=[str(ROOT/'bootloops-lean')]
 if output: cmd+=['-o',str(dest.with_suffix('.olean'))]
 cmd += [str(dest)]
 start=time.perf_counter()
 proc=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
 log=LOG/(name+'.log'); log.write_text(proc.stdout)
 row=dict(name=name,source=str(source.relative_to(ROOT)),source_sha256=sha(source),log=str(log.relative_to(ROOT)),log_sha256=sha(log),exit_code=proc.returncode,expected=expected,seconds=time.perf_counter()-start)
 if explicit: row['explicit_false']=bool(re.search(r'decide.*false|false.*decide',proc.stdout,re.S|re.I))
 rows.append(row); save()
 assert proc.returncode==expected,(name,proc.stdout)
 if explicit: assert row['explicit_false'],(name,proc.stdout)
 print(name,proc.returncode,round(row['seconds'],3),flush=True)

# Dependence order comes from the actual import graph, not the author's order.
sources={Path(p).stem:ROOT/p for p in data['source_pins']}
done=set()
def compile_module(name,active=()):
 assert name not in active,('cycle',active,name)
 if name in done:return
 s=sources[name]
 for imp in re.findall(r'^import (\S+)$',s.read_text(),re.M):
  if imp!='Std':
   assert imp in sources,('unapproved import',imp)
   compile_module(imp,active+(name,))
 run(name,s); done.add(name)
for name in sources:compile_module(name)
for r in data['builds_and_controls']:
 if r['name'] in done:continue
 run(r['name'],ROOT/r['source'],r['expected_exit'],r.get('explicit_false',False),False)
# Axioms are re-read from the fresh build's print output, not status flags.
axiom=(LOG/'AllAxioms.log').read_text()
reports=re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",axiom,re.S)
assert len(reports)==len(data['declarations']),('axiom coverage',len(reports),len(data['declarations']))
allowed={'propext','Classical.choice','Quot.sound'}
for name,axs in reports:
 assert set(a.strip() for a in axs.split(',') if a.strip())<=allowed,(name,axs)
for p,h in data['source_pins'].items():assert sha(ROOT/p)==h
receipt=json.loads((HERE/'rebuild-receipt.json').read_text())
receipt.update(status='pass',axiom_reports_checked=len(reports),standard_axioms_only=True,script_sha256=sha(Path(__file__)),semantic_negative_controls=sum(bool(r.get('explicit_false')) for r in rows),malformed_separate=True)
(HERE/'rebuild-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','axiom_reports_checked','semantic_negative_controls']}))
