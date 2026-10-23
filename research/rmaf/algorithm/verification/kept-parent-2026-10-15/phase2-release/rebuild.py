"""Nonauthor source-only kept-parent replay; copies only exact manifest members."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json,os,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[6];HERE=Path(__file__).resolve().parent
AUTHOR=ROOT/'research/rmaf/algorithm/universal233/kept_parent'
MANIFEST=AUTHOR/'HANDOFF-MANIFEST-v1.json';PIN='a2506163a4e1231b02eb785b5a4275167ef657ccd1becb35e956550c19982d70'
CERT=ROOT/'results/algorithm-universal233-kept-20261015T094548Z/certificate.json'
HELPER=ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/phase2-release/rebuild.py'
BUILD=HERE/'isolated';DEST=ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-rebuild-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def helper():
    ready=json.loads((HERE.parent/'CONTROL-FREEZE-v1.json').read_text());assert sha(HELPER)==ready['reuse_helper_sha256']
    spec=importlib.util.spec_from_file_location('own_frozen_rebuild_helper',HELPER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    assert sha(MANIFEST)==PIN
    manifest=json.loads(MANIFEST.read_text());pins={x['path']:x['sha256'] for x in manifest['entries']}
    for p,s in pins.items():assert sha(ROOT/p)==s,p
    cert=json.loads(CERT.read_text());assert str(CERT.relative_to(ROOT)) in pins
    primary=list(cert['compiled_hashes']);assert len(primary)==41
    mods=primary+['LiteralControls','Interfaces','CheckAPI']
    BUILD.mkdir(exist_ok=False);sources=[];imports=[]
    for name in mods:
        p=AUTHOR/(name+'.lean')
        if not p.exists():p=AUTHOR/'proof-build'/(name+'.lean')
        rel=str(p.relative_to(ROOT));assert rel in pins
        if name in cert['compiled_hashes']:assert pins[rel]==cert['compiled_hashes'][name]
        out=BUILD/(name+'.lean');out.write_bytes(p.read_bytes())
        sources.append({'module':name,'original':rel,'realpath':str(p.resolve()),'copy':str(out.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size})
        for group in re.findall(r'^import\s+([^\n]+)',out.read_text(),re.M):
            for imp in group.split():
                assert imp in ('Lean','Std') or imp in mods,(name,imp)
                imports.append({'module':name,'import':imp,'standard':imp in ('Std','Lean')})
    H=helper();result={'stage':'FRESH_SOURCE_ONLY_REBUILD','utc':datetime.now(timezone.utc).isoformat(),'author_manifest_sha256':PIN,'source_receipt_sha256':sha(CERT),'sources':sources,'imports':imports,'copied_scientific_oleans':False,'source_modules':len(mods),'builds':[],'all_main_milestones':'OPEN','replication_count_added':0}
    def save():DEST.write_text(json.dumps(result,indent=2)+'\n')
    runtime={}
    for arg in ('--version','--print-prefix'):
        p=subprocess.run([str(ROOT/'bootloops-lean'),arg],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);assert p.returncode==0;runtime[arg]=p.stdout.strip()
    prefix=Path(runtime['--print-prefix']);originpaths=[ROOT/'bootloops-lean',prefix/'bin/lean',prefix/'lib/lean/Std.olean',prefix/'lib/lean/Lean.olean']
    runtime['pins']={str(p):sha(p) for p in originpaths};result['runtime']=runtime;save()
    start=time.monotonic()
    for i,name in enumerate(mods):
        r=H.run(BUILD,name,['-o',name+'.olean']);result['builds'].append(r);save()
        print('BUILD',i+1,len(mods),name,r['exit'],round(r['seconds'],3),flush=True)
        assert r['exit']==0,r
        if i==2:
            result['timing_pilot']={'modules':3,'seconds':time.monotonic()-start,'fixed_total_modules':len(mods),'projection_seconds':(time.monotonic()-start)*len(mods)/3,'assumption':'Fixed already measured author stack; size-linear estimate is conservative since first RMAF compile dominates. Stop on any scientific/source mismatch.'};save()
    result['positive_seconds']=time.monotonic()-start
    (BUILD/'FreshAllAudit.lean').write_text(H.audit_text(mods,'\nimport '.join(mods)))
    r=H.run(BUILD,'FreshAllAudit');result['audit_build']=r;save();assert r['exit']==0
    audit=H.parse_audit(BUILD/'FreshAllAudit.log',primary+['LiteralControls'])
    # Interfaces and CheckAPI intentionally contain only #check/#print commands,
    # with no new declaration; nevertheless both are imported and inventoried.
    assert audit['counts'].keys()==dict.fromkeys(primary+['LiteralControls']).keys()
    audit['zero_declaration_modules']={m:sum(x['module']==m for x in audit['rows']) for m in ('Interfaces','CheckAPI')}
    assert all(v==0 for v in audit['zero_declaration_modules'].values())
    result['audit']=audit;assert not audit['forbidden']
    result['source_unchanged']=all(sha(ROOT/x['copy'])==x['sha256'] and sha(ROOT/x['original'])==x['sha256'] for x in sources)
    assert result['source_unchanged'];result['olean_hashes']={m:sha(BUILD/(m+'.olean')) for m in mods}
    result['status']='PASS_FRESH_SOURCE_ONLY_AND_FULL_ORIGIN';save();print('AUDIT',audit['total'],audit['axiom_union'],flush=True)
if __name__=='__main__':main()
