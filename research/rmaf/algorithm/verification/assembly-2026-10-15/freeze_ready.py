"""Seal prerelease readiness, preserving every prior completed core file."""
from pathlib import Path
import json,hashlib,datetime,subprocess,os
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    f=json.loads((HERE/'FREEZE-v1.json').read_text())
    for r in f['before_execution_files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
    a=json.loads((HERE/'ADDENDUM-FREEZE-v1.json').read_text())
    for r in a['files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
    old=ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/phase2-release/REVIEW-MANIFEST-v1.json'
    assert sha(old)=='c4c316fcd484d51cc1cebafbf69a9fa9b7500e56cc93b4617fb33326c69af7db'
    previous=json.loads(old.read_text());assert previous['file_count']==377
    for r in previous['files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
    receipts=[]
    for tag in ['pilot','full','addendum','toy-gates']:
        p=ROOT/f'research/rmaf/results/algorithm-assembly-prerelease-review-{tag}-v1.json'
        d=json.loads(p.read_text());assert d['status'].startswith('PASS')
        assert d['candidate_contact']==False if 'candidate_contact' in d else not d['candidate_compiled']
        receipts.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p),'status':d['status']})
    runtime={}
    for flag in ['--version','--print-prefix']:
        p=subprocess.run([str(ROOT/'bootloops-lean'),flag],cwd=HERE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        assert p.returncode==0;runtime[flag]=p.stdout.strip()
        (HERE/('runtime'+flag+'.log')).write_text(p.stdout)
    prefix=Path(runtime['--print-prefix'])
    runtime['origin_files']={str(p):sha(p) for p in [ROOT/'bootloops-lean',prefix/'bin/lean',prefix/'lib/lean/Std.olean',prefix/'lib/lean/Lean.olean']}
    status={'stage':'READY_PRE_CANDIDATE','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'candidate_contact':False,'candidate_compilation':False,'root_release_pending':True,
      'all_main_milestones':'OPEN','replication_count_added':0,
      'expectations_frozen_before_execution':True,'receipts':receipts,
      'previous_completed_review':{'manifest':str(old.relative_to(ROOT)),'sha256':sha(old),'files':377,'all_unchanged':True},
      'runtime':runtime,'provenance':'CONTACTS-v1.md','later_gate':'LATER-RELEASE-GATE.md',
      'interpretation':'finite preparation gates only; no candidate theorem/algorithm/base acceptance'}
    p=ROOT/'research/rmaf/results/algorithm-assembly-prerelease-review-ready-v1.json'
    p.write_text(json.dumps(status,indent=2)+'\n')
    files=sorted(q for q in HERE.rglob('*') if q.is_file() and '__pycache__' not in q.parts and q.name not in ['READY-MANIFEST-v1.json','READY-MANIFEST-v1.sha256'])
    files+=sorted((ROOT/'research/rmaf/results').glob('algorithm-assembly-prerelease-review-*-v1.json'))
    files=sorted(set(files))
    entries=[{'path':str(q.relative_to(ROOT)),'realpath':str(q.resolve()),'sha256':sha(q),'bytes':q.stat().st_size} for q in files]
    manifest={**status,'immutable':True,'files':entries,'file_count':len(entries),'bytes':sum(q['bytes'] for q in entries)}
    p=HERE/'READY-MANIFEST-v1.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
    digest=sha(p);q=HERE/'READY-MANIFEST-v1.sha256';q.write_text(digest+'  READY-MANIFEST-v1.json\n')
    for r in entries:assert sha(ROOT/r['path'])==r['sha256']
    for r in files+[p,q]:r.chmod(0o444)
    print('READY FROZEN',len(entries),'files',manifest['bytes'],'bytes')
    print('SHA256',digest)

if __name__=='__main__':main()
