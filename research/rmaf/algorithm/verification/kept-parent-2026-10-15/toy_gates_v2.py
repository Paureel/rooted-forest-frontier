"""Preregistered Std/Lean-only gates; NEVER loads or compiles a candidate."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,importlib.util,json,sys,time
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    frozen=json.loads((HERE/'TOY-FREEZE-v2.json').read_text())
    for row in frozen['files']: assert sha(ROOT/row['path'])==row['sha256']
    helper=ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/phase2-release/rebuild.py'
    assert sha(helper)==frozen['reuse_helper_sha256']
    spec=importlib.util.spec_from_file_location('frozen_own_origin_helper',helper)
    H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
    build=HERE/'toy-build-v2';build.mkdir(exist_ok=False)
    clean='''import Std
namespace KeptParentToy
structure Cell where
  value : Nat
private theorem hidden : True := True.intro
def branch : Nat → Nat
  | 0 => 0
  | n+1 => branch n + 1
#check branch.eq_1
theorem visible : branch 0 = 0 := rfl
end KeptParentToy
'''
    sources={'Clean':clean,
      'UnusedPublic':'import Clean\naxiom unrelatedPublic : False\ntheorem innocent : True := True.intro\n',
      'UnusedPrivate':'import Clean\nprivate axiom unrelatedPrivate : False\ntheorem innocent : True := True.intro\n',
      'UsedPrivate':'import Clean\nprivate axiom usedPrivate : False\ntheorem contaminated : True := False.elim usedPrivate\n'}
    rows=[];start=time.monotonic()
    for name,text in sources.items():
        (build/(name+'.lean')).write_text(text)
        r=H.run(build,name,['-o',name+'.olean']);assert r['exit']==0,r
        mods=['Clean'] if name=='Clean' else ['Clean',name]
        top='\nimport '.join(mods)
        (build/(name+'Audit.lean')).write_text(H.audit_text(mods,top))
        a=H.run(build,name+'Audit');assert a['exit']==0,a
        audit=H.parse_audit(build/(name+'Audit.log'),mods)
        priv=[x for x in audit['rows'] if x['module']=='Clean' and x['name'].startswith('_private.')]
        generated=[x for x in audit['rows'] if x['module']=='Clean' and x['name'].endswith('branch.match_1')]
        assert priv and generated,'private/generated clean origin missing'
        if name=='Clean':assert not audit['forbidden'] and not any(x['kind']=='axiom' for x in audit['rows'])
        else:
            assert audit['forbidden'] and any(x['module']==name and x['kind']=='axiom' for x in audit['rows'])
            if name=='UnusedPrivate':assert any(x['module']==name and x['name'].startswith('_private.') and x['kind']=='axiom' for x in audit['rows'])
            if name=='UsedPrivate':assert any(x['name']=='contaminated' and x['axioms'] for x in audit['rows'])
        rows.append({'name':name,'source_sha256':sha(build/(name+'.lean')),'build':r,'audit_build':a,'audit':audit,'expected_custom_axiom_rejection':name!='Clean','private_origins':len(priv),'generated_matcher_origins':len(generated)})
        print(name,audit['total'],len(audit['forbidden']),flush=True)
    (build/'FalseProp.lean').write_text('import Std\nexample : (2 : Nat) = 3 := by decide\n')
    f=H.run(build,'FalseProp');log=(build/'FalseProp.log').read_text()
    assert f['exit']!=0 and 'proved that the proposition' in log and 'is false' in log and 'failed to reduce' not in log
    (build/'TrueProp.lean').write_text('import Std\nexample : (2 : Nat) = 2 := by decide\n')
    t=H.run(build,'TrueProp');assert t['exit']==0
    result={'status':'PASS_PRE_CANDIDATE_TOY_ORIGIN_GATES','utc':datetime.now(timezone.utc).isoformat(),'candidate_contact':False,'candidate_compilation':False,'custom_axiom_toys_only':True,'positive_clean_twin':True,'private_generated_complete':True,'negative_custom_axiom_catches':3,'explicit_false_prop_catches':1,'rows':rows,'false_prop':f,'true_prop':t,'elapsed_seconds':time.monotonic()-start,'all_main_milestones':'OPEN','replication_count_added':0}
    dest=ROOT/'research/rmaf/results/algorithm-kept-parent-prerelease-toy-gates-v2.json';dest.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],result['elapsed_seconds'],flush=True)
if __name__=='__main__':main()
