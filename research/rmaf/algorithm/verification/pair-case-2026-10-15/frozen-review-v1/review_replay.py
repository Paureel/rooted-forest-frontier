#!/usr/bin/env python3
"""One-shot source-bound independent G/E replay. No author runner imports.

Lean's module-origin and collectAxioms API usage was learned by reading the
released audit sources. This is a fresh driver/detector, not an independent
kernel or an independently invented axiom-audit mechanism.
"""
import hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
RMAF=ROOT/'research/rmaf'
BUILD=HERE/'isolated-review-v1'
OUT=RMAF/'results/algorithm-pair-case-fresh-review-lean-v1.json'
G=RMAF/'algorithm/pair_case/geometry'
E=RMAF/'results/algorithm-pair-case-exchange-20261015T083439Z'
SCIENTIFIC_G=['RMAF','Geometry','Bridge','Selector','Controls']
SCIENTIFIC_E=['RMAF','Geometry','Bridge','Restriction','Cluster','Descendant','Forest','Surgery','Count','Parents','Exchange','SourceEdge','Controls','T1']
state={'phase':'RELEASED-NONAUTHOR-REPLAY','scope':'G/E only; all main algorithm milestones OPEN','hash_checks':[],'runs':[],'audits':{},'control_provenance':'Own expectations frozen before release. Origin/collectAxioms APIs shared with released audit sources; no author Python replay or checker executed.'}

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save():OUT.write_text(json.dumps(state,indent=2)+'\n')
def checked(p,h,kind):
    actual=digest(p);state['hash_checks'].append({'path':str(p.relative_to(ROOT)),'expected':h,'actual':actual,'kind':kind})
    assert actual==h,(p,actual,h)

def code_only(text):
    # Nested block comments, line comments and strings are not source tokens.
    out=[];i=0;depth=0;string=False
    while i<len(text):
        if depth:
            if text[i:i+2]=='/-':depth+=1;i+=2
            elif text[i:i+2]=='-/':depth-=1;i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif string:
            if text[i]=='\\':i+=2
            elif text[i]=='"':string=False;i+=1
            else:i+=1
        elif text[i:i+2]=='/-':depth=1;i+=2
        elif text[i:i+2]=='--':
            while i<len(text) and text[i]!='\n':i+=1
        elif text[i]=='"':string=True;i+=1
        else:out.append(text[i]);i+=1
    assert not depth and not string,'unterminated source comment/string'
    return ''.join(out)

def compile_one(folder,module,expected='compile'):
    start=time.monotonic();env=os.environ.copy();env['LEAN_PATH']=str(folder)
    cmd=[str(ROOT/'bootloops-lean'),'-o',module+'.olean',module+'.lean']
    try:
        run=subprocess.run(cmd,cwd=folder,env=env,text=True,capture_output=True,timeout=40)
        rc=run.returncode;log=run.stdout+run.stderr
    except subprocess.TimeoutExpired as ex:
        rc=124;log=(ex.stdout or b'').decode() if isinstance(ex.stdout,bytes) else (ex.stdout or '')
        log+='\nOPEN: local 40-second timeout\n'
    (folder/(module+'.log')).write_text(log)
    row={'directory':str(folder.relative_to(ROOT)),'module':module,'returncode':rc,'seconds':time.monotonic()-start,'expected':expected,'log_sha256':digest(folder/(module+'.log'))}
    state['runs'].append(row);save();print(json.dumps(row),flush=True)
    if expected=='compile':assert rc==0,(module,log[-3000:])
    elif expected=='false':assert rc!=0 and 'proposition' in log and 'false' in log and 'decide' in log,(module,log[-3000:])
    elif expected=='audit-reject':assert rc!=0 and 'FRESH_AUDIT_REJECT' in log,(module,log[-3000:])
    return log

def audit_source(imports,modules):
    # Independently emit a complete inventory and reject on every bad record.
    return '\n'.join('import '+m for m in imports)+'''
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names : List Name := MODULES
  let standards : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut found : List Name := []
  let mut bad : Nat := 0
  for entry in env.constants.toList do
    let n := entry.1
    let info := entry.2
    if let some index := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[index.toNat]!
      if names.contains origin then
        found := origin :: found
        let dependencies ← collectAxioms n
        let forbidden := dependencies.toList.filter (fun a => !standards.contains a)
        let invalid := info.isAxiom || info.isUnsafe || !forbidden.isEmpty
        if invalid then bad := bad + 1
        logInfo m!"FRESH|{origin}|{n}|{info.isAxiom}|{info.isUnsafe}|{String.intercalate "," (dependencies.toList.map Name.toString)}|{invalid}"
  for module in names do
    let count := (found.filter (· == module)).length
    logInfo m!"FRESH_COUNT|{module}|{count}"
    if count == 0 then throwError m!"FRESH_MISSING_ORIGIN {module}"
  logInfo m!"FRESH_BAD|{bad}"
  if bad > 0 then throwError "FRESH_AUDIT_REJECT"
'''.replace('MODULES','['+','.join('`'+m for m in modules)+']')

def audit(folder,module,imports,modules,reject=False):
    (folder/(module+'.lean')).write_text(audit_source(imports,modules))
    log=compile_one(folder,module,'audit-reject' if reject else 'compile')
    rows=[];counts={}
    for line in log.splitlines():
        if line.startswith('FRESH|'):
            _,origin,name,isax,unsafe,axs,bad=line.split('|')
            rows.append({'origin':origin,'name':name,'is_axiom':isax=='true','unsafe':unsafe=='true','axioms':axs.split(',') if axs else [],'rejected':bad=='true'})
        if line.startswith('FRESH_COUNT|'):
            _,origin,count=line.split('|');counts[origin]=int(count)
    assert rows and sum(counts.values())==len(rows)
    bad=[r for r in rows if r['rejected']]
    assert bool(bad)==reject
    state['audits'][folder.name+'/'+module]={'counts':counts,'total':len(rows),'bad':bad,'all_declarations':rows}
    save();return rows

def main():
    assert not BUILD.exists(),'fresh build directory required'
    BUILD.mkdir();OUT.parent.mkdir(exist_ok=True)
    checked(G/'DELIVERY.sha256','1e2179095be830a78c4dffb25ae816895f366ae9e6f56e2d12186daf12b2bb2d','root-release seal')
    for line in (G/'DELIVERY.sha256').read_text().splitlines():
        h,p=line.split(None,1);checked(ROOT/p.strip(),h,'G delivery')
    checked(E/'manifest.json','5815d0f97d7a70d63489997bece0d6ee2a90371624d050bbac3e42362ae97f3b','root-release seal')
    em=json.loads((E/'manifest.json').read_text())
    descriptors=[]
    for p,r in em['files'].items():
        checked(E/p,r['sha256'],'E snapshot')
        if r['origin'].startswith('research/'):
            checked(ROOT/r['origin'],r['sha256'],'E origin')
        else:
            assert p in ('source/CleanTwinAudit.lean','source/AxiomPlantAudit.lean')
            descriptors.append({'file':p,'origin_descriptor':r['origin'],'actual_contents':(E/p).read_text()})
    state['nonpath_origin_descriptors']=descriptors
    for folder,modules,src in [(BUILD/'g',SCIENTIFIC_G,G/'lean'),(BUILD/'e',SCIENTIFIC_E,E/'source')]:
        folder.mkdir()
        for m in modules:
            text=(src/(m+'.lean')).read_text()
            tokens=code_only(text)
            assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',tokens),m
            shutil.copyfile(src/(m+'.lean'),folder/(m+'.lean'))
    state['copied_source_hashes']={str(p.relative_to(BUILD)):digest(p) for p in BUILD.glob('*/*.lean')};save()
    own=BUILD/'own';own.mkdir()
    (own/'CleanControl.lean').write_text('theorem ownClean : True := True.intro\n#print axioms ownClean\n')
    (own/'FalseControl.lean').write_text('theorem ownImpossible : False := by decide\n')
    (own/'PlantDependency.lean').write_text('axiom ownUnusedFalse : False\nprivate axiom ownPrivateFalse : False\nprivate theorem ownHiddenFalse : False := ownPrivateFalse\ntheorem ownExportedFalse : False := ownPrivateFalse\n')
    (own/'PlantClient.lean').write_text('import PlantDependency\ntheorem ownImportedFalse : False := ownExportedFalse\n#print axioms ownImportedFalse\n')
    compile_one(own,'CleanControl');audit(own,'CleanAudit',['CleanControl'],['CleanControl'])
    compile_one(own,'FalseControl','false')
    compile_one(own,'PlantDependency');compile_one(own,'PlantClient')
    bad=audit(own,'PlantAudit',['PlantClient'],['PlantDependency','PlantClient'],True)
    assert len([r for r in bad if r['is_axiom']])==2
    assert any(r['name'].startswith('_private.') and r['rejected'] for r in bad)
    assert any(r['origin']=='PlantClient' and r['rejected'] for r in bad)
    for folder,modules in [(BUILD/'g',SCIENTIFIC_G),(BUILD/'e',SCIENTIFIC_E)]:
        for module in modules:compile_one(folder,module)
        audit(folder,'FreshAudit',[modules[-1]],modules)
    for m in ['FalseSharedThree','FalseRootUp','FalseSuppressed','FalseClear','FalseAbsent']:
        shutil.copyfile(G/'lean'/(m+'.lean'),BUILD/'g'/(m+'.lean'));compile_one(BUILD/'g',m,'false')
    for m in ['FalseWholeB','FalseWholeBCut','FalseNoCluster','FalseBoundary','FalseAbsent']:
        shutil.copyfile(E/'source'/(m+'.lean'),BUILD/'e'/(m+'.lean'));compile_one(BUILD/'e',m,'false')
    state['verdict']='ISOLATED-SOURCE-REPLAY-AND-OWN-DETECTORS-PASSED; semantic/interface verdict pending'
    save()

if __name__=='__main__':
    try:main()
    except Exception as ex:
        state['verdict']='OPEN-REPLAY-OR-DETECTOR-FAILURE';state['error']=repr(ex);save();raise
