"""Exact source-only isolated rebuilds for the two separately released packages."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json,re,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[6];HERE=Path(__file__).resolve().parent
PACKAGES={'maf':('maf_scheduler/MAF-SCHEDULER-MANIFEST-v1.json','616fc379859f92eea35b73fd3334c88c5754cc1ecf1a9f8698b082b14b071ebd'), 'groups':('forest_groups/FOREST-GROUPS-MANIFEST-v2.json','23ddfc690c8701a12ca18a17faa75133d6c04759211e07f63cfeb171eabcdfc9')}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def helper():
 p=ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/phase2-release/rebuild.py';f=json.loads((HERE.parent/'CONTROL-FREEZE-v1.json').read_text());assert sha(p)==f['reuse_helper_sha256']
 s=importlib.util.spec_from_file_location('frozen_own_audit_helper',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def main():
 arm=sys.argv[1];rel,pin=PACKAGES[arm];manifest=ROOT/'research/rmaf/algorithm/universal233'/rel;assert sha(manifest)==pin;m=json.loads(manifest.read_text());pins={x['path']:x['sha256'] for x in m['immutable_files']}
 for p,s in pins.items():assert sha(ROOT/p)==s,p
 certpath=ROOT/m['canonical_receipt'];cert=json.loads(certpath.read_text());modules=cert['positive_order'] if arm=='maf' else cert['source_modules']
 build=HERE/('isolated-'+arm);build.mkdir(exist_ok=False);rows=[];imports=[]
 adaptations={x['module']:x for x in cert.get('adaptations',[])}
 inputs={x['module']:x for x in cert.get('source_inputs',[])}
 for module in modules:
  p=certpath.parent/(module+'.lean');assert str(p.relative_to(ROOT)) in pins and sha(p)==pins[str(p.relative_to(ROOT))]
  adapted=p.read_text();mapping={};original=None;expected=None
  if arm=='maf':
   x=inputs[module];original=ROOT/x['source'];assert sha(original)==x['original_sha256'];expected=x['copy_sha256']
   if x['first_import_adapter']:mapping=dict([x['first_import_adapter']])
  elif module in adaptations:
   x=adaptations[module];original=ROOT/x['path'];assert sha(original)==x['sha256'];mapping=x['adaptations'];expected=x['adapted_sha256']
  else:
   original=manifest.parent/(module+'.lean');assert str(original.relative_to(ROOT)) in pins and sha(original)==pins[str(original.relative_to(ROOT))];expected=sha(original)
  before=original.read_text();lines=before.splitlines(keepends=True);patched=[]
  for line in lines:
   if line.startswith('import '):
    newline='\n' if line.endswith('\n') else '';line='import '+' '.join(mapping.get(t,t) for t in line.strip().split()[1:])+newline
   patched.append(line)
  assert ''.join(patched)==adapted,(arm,module,'non-import source body mismatch')
  assert sha(p)==expected
  out=build/(module+'.lean');out.write_bytes(p.read_bytes())
  rows.append({'module':module,'source':str(original.relative_to(ROOT)),'source_realpath':str(original.resolve()),'source_sha256':sha(original),'frozen_copy':str(p.relative_to(ROOT)),'copy_sha256':sha(p),'local_copy':str(out.relative_to(ROOT)),'import_only_mapping':mapping,'all_other_source_bytes_unchanged':True})
  for group in re.findall(r'^import\s+([^\n]+)',adapted,re.M):
   for imp in group.split():assert imp in ('Std','Lean') or imp in modules,(arm,module,imp);imports.append({'module':module,'import':imp})
 H=helper();result={'arm':arm,'utc':datetime.now(timezone.utc).isoformat(),'status':'BUILDING','author_manifest_sha256':pin,'canonical_receipt_sha256':sha(certpath),'modules':modules,'sources':rows,'imports':imports,'copied_scientific_oleans':False,'builds':[],'all_main_milestones':'OPEN','replication_count_added':0};dest=ROOT/f'research/rmaf/results/algorithm-maf-grouped-fresh-review-{arm}-rebuild-v1.json'
 def save():dest.write_text(json.dumps(result,indent=2)+'\n')
 start=time.monotonic()
 for i,name in enumerate(modules):
  r=H.run(build,name,['-o',name+'.olean']);result['builds'].append(r);save();print(arm,i+1,len(modules),name,r['exit'],round(r['seconds'],3),flush=True);assert r['exit']==0,r
  if i==2:result['pilot_projection']={'modules':3,'seconds':time.monotonic()-start,'fixed_modules':len(modules),'linear_seconds':(time.monotonic()-start)*len(modules)/3,'assumption':'fixed released stack; first RMAF compile dominates; no census'};save()
 (build/'FreshAudit.lean').write_text(H.audit_text(modules,'\nimport '.join(modules)));a=H.run(build,'FreshAudit');result['audit_build']=a;save();assert a['exit']==0
 parsed=H.parse_audit(build/'FreshAudit.log',modules);assert not parsed['forbidden'];result['audit']=parsed
 expected_counts=cert['module_counts'] if arm=='maf' else cert['module_origin_counts'];assert parsed['counts']==expected_counts,(parsed['counts'],expected_counts)
 result['olean_hashes']={n:sha(build/(n+'.olean')) for n in modules};result['status']='PASS_SOURCE_ONLY_AND_ALL_ORIGINS';result['seconds']=time.monotonic()-start;save();print('DONE',arm,parsed['total'],parsed['axiom_union'],flush=True)
if __name__=='__main__':main()
