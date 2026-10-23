"""Correct two v1 rejection classifications; preserve every old source/log."""
import json
from rebuild import ROOT,HERE,run,digest

def main():
    b=HERE/'isolated-source'
    prefix='''import RationalMass
open Universal233.CoreProgram Universal233.SourceCoverage
def actual := (generate Controls.crossed Controls.parity 2).outputs
def duplicated := [actual.getD 0 ⟨[],[]⟩,actual.getD 0 ⟨[],[]⟩,actual.getD 1 ⟨[],[]⟩]
theorem cleanMass2 : rawQMass 2 duplicated = mkRat 3 4 := by decide +kernel
theorem cleanMass233 : rawQMass (233/100) duplicated = mkRat 30000 54289 := by decide +kernel
theorem fractionHalf : (1/2 : Rat) = mkRat 1 2 := by decide +kernel
theorem fractionWrong233 : (20000/54289 : Rat) = mkRat 20000 54289 := by decide +kernel
'''
    (b/'FreshMassCleanV3.lean').write_text(prefix)
    clean=run(b,'FreshMassCleanV3');assert clean['exit']==0,clean
    rows=[]
    for m,claim,rewrite,ground in [
        ('FalseOmittedMass2V3','rawQMass 2 duplicated = 1/2','cleanMass2, fractionHalf','mkRat 3 4 = mkRat 1 2'),
        ('FalseOmittedMass233V3','rawQMass (233/100) duplicated = 20000/54289','cleanMass233, fractionWrong233','mkRat 30000 54289 = mkRat 20000 54289')]:
        (b/(m+'.lean')).write_text(prefix+f'\nexample : {claim} := by\n  rw [{rewrite}]\n  decide\n')
        r=run(b,m);s=(b/(m+'.log')).read_text()
        assert r['exit'] and 'proved that the proposition' in s and 'is false' in s
        assert 'failed to reduce' not in s and 'synthesize' not in s
        rows.append({**r,'source_sha256':digest(b/(m+'.lean')),'rejected_false_proposition':True})
    old=ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-rejections-v1.json'
    report=json.loads(old.read_text())
    inconclusive=[];kept=[]
    for r in report['records']:
        if r['module'] in ['FalseOmittedMass2','FalseOmittedMass233']:
            inconclusive.append({**r,'rejected_false_proposition':False,
              'classification':'INCONCLUSIVE_REDUCTION_STUCK; not counted; superseded by V2 explicit wrong mkRat comparison'})
        else:
            if r.get('rejected_false_proposition'):
                s=(ROOT/r['log']).read_text()
                assert 'proved that the proposition' in s and 'is false' in s and 'failed to reduce' not in s
            kept.append(r)
    report['records']=kept+[clean]+rows
    report['supersedes_receipt']=str(old.relative_to(ROOT));report['superseded_sha256']=digest(old)
    report['retained_inconclusive_attempts']=inconclusive
    report['retained_adapter_failure']={'module':'FalseOmittedMass2V2',
      'source_sha256':digest(b/'FalseOmittedMass2V2.lean'),
      'log_sha256':digest(b/'FalseOmittedMass2V2.log'),
      'classification':'change failed because rational division is not definitionally mkRat under tactic transparency; not counted'}
    report['correction']='v1 validator matched the word false in a reduction-stuck diagnostic. Two mass records were therefore misclassified. V2 requires the explicit proved-that-the-proposition / is-false diagnostic and rejects reduction-stuck output.'
    report['explicit_false_proposition_count']=sum(r.get('rejected_false_proposition',False) for r in report['records'])
    assert report['explicit_false_proposition_count']==7
    report['status']='PASS_CORRECTED_REJECTION_CONTROLS'
    (ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-rejections-v2.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],'7 actual false propositions; 2 old inconclusive attempts retained')

if __name__=='__main__':main()
