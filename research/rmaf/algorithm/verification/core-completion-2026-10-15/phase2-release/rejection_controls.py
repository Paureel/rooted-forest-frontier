"""Actual Lean false propositions and full-origin/private-axiom sentinels."""
import json, shutil, subprocess, os
from pathlib import Path
from rebuild import ROOT,HERE,run,digest,audit_text,parse_audit

def main():
    b=HERE/'isolated-source'; records=[]
    for t in sorted((HERE.parent/'frozen-v1/later-controls').glob('*.template')):
        m=t.name.split('.')[0];(b/(m+'.lean')).write_bytes(t.read_bytes())
        r=run(b,m);s=(b/(m+'.log')).read_text()
        assert r['exit']!=0 and 'decide' in s and 'false' in s, (m,s)
        assert not any(x in s for x in ('unknown module','unknown identifier','failed to synthesize','unexpected token'))
        records.append({**r,'frozen_template_sha256':digest(t),'rejected_false_proposition':True})
    positives='''import RationalMass
open Universal233.CoreProgram Universal233.SourceCoverage
example : (generate Controls.crossed Controls.parity 3).outputs.length = 2 := by decide
example : (Controls.costs (generate Controls.crossed Controls.parity 3)).all (fun c => decide (2 ≤ c)) = true := by decide
example : (combine (generate Controls.crossed Controls.parity 3) (generate Controls.crossed Controls.parity 3)).outputs.length = 4 := by decide
def refines (fine coarse : List (List Nat)) : Bool := fine.all (fun b => coarse.any (fun a => b.all a.contains))
example : refines [[0],[1],[2]] [[0,1],[2]] = true := by decide
def os := (generate Controls.crossed Controls.parity 2).outputs
def duplicated := [os.getD 0 ⟨[],[]⟩,os.getD 0 ⟨[],[]⟩,os.getD 1 ⟨[],[]⟩]
example : (duplicated.map (fun o => o.sourceCuts.length)).sum = 6 := by decide
example : rawQMass 2 duplicated = 3/4 := by decide
example : rawQMass (233/100) duplicated = 30000/54289 := by decide
'''
    positives=positives.replace(':= by decide',':= by decide +kernel')
    (b/'FreshCleanTwins.lean').write_text(positives);r=run(b,'FreshCleanTwins');assert r['exit']==0;records.append(r)
    for m,claim in [('FalseOmittedCost','(duplicated.map (fun o => o.sourceCuts.length)).sum = 4'),
                    ('FalseOmittedMass2','rawQMass 2 duplicated = 1/2'),
                    ('FalseOmittedMass233','rawQMass (233/100) duplicated = 20000/54289')]:
        (b/(m+'.lean')).write_text(positives+'\nexample : '+claim+' := by decide +kernel\n')
        r=run(b,m);s=(b/(m+'.log')).read_text();assert r['exit'] and 'false' in s and 'decide' in s
        records.append({**r,'rejected_false_proposition':True})
    # Both toy modules compile. The private custom axiom must nevertheless be
    # found by full originating-module enumeration, even without an exported name.
    (b/'FreshCleanPlant.lean').write_text('import Std\nprivate theorem hiddenTrue : True := True.intro\nprivate def hiddenNat : Nat := 3\n')
    (b/'FreshDirtyPlant.lean').write_text('import Std\nprivate axiom hiddenDebt : False\nprivate theorem hiddenFalse : False := hiddenDebt\n')
    audits={}
    for m in ('FreshCleanPlant','FreshDirtyPlant'):
        r=run(b,m,['-o',m+'.olean']);assert not r['exit'];records.append(r)
        a=m+'Audit';(b/(a+'.lean')).write_text(audit_text([m],m));r=run(b,a);assert not r['exit'];records.append(r)
        audits[m]=parse_audit(b/(a+'.log'),[m])
    assert not audits['FreshCleanPlant']['forbidden']
    assert audits['FreshDirtyPlant']['forbidden']
    assert all('_private.' in row['name'] for row in audits['FreshDirtyPlant']['rows'])
    # Delete a PRIVATE audit record, keeping the compiler emitted total. A
    # namespace-only/public-only scanner would fail this deliberate omission.
    original=(b/'FreshAudit.log').read_text();lines=original.splitlines()
    idx=next(i for i,s in enumerate(lines) if s.startswith('FRESH|') and '|_private.' in s)
    missing=lines.pop(idx);(b/'FreshMissingPrivate.log').write_text('\n'.join(lines)+'\n')
    mods=json.loads((ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-source-rebuild-v1.json').read_text())['audit']['counts']
    caught=False
    try:parse_audit(b/'FreshMissingPrivate.log',list(mods))
    except AssertionError as e:caught=str(e)=='missing audit record'
    assert caught
    # Source pin corrupt twin: only a separate control copy is edited.
    p=b/'CoreProgram.lean';copy=b/'FreshDriftTwin.txt';copy.write_bytes(p.read_bytes()+b'\n-- deliberate drift\n')
    source_drift_caught=digest(p)!=digest(copy);assert source_drift_caught
    report={'status':'PASS_REJECTION_CONTROLS','records':records,'toy_audits':audits,
      'private_custom_axiom_caught':True,'missing_private_record_caught':caught,
      'omitted_private_record':missing,'source_pin_drift_caught':source_drift_caught,
      'candidate_sources_mutated':False,'explicit_false_proposition_count':7,
      'positive_twin_assertion_count':7,'replication_count_added':0}
    (ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-rejections-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],'7 false propositions rejected; private custom axiom/missing record/source drift caught')

if __name__=='__main__':main()
