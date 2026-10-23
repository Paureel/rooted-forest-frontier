"""Check the one duplicate generated declaration before origin reconciliation."""
import json
from rebuild import ROOT,HERE,run,digest

def main():
    reports=[]
    for folder,top in [('isolated-source','Controls'),('isolated-cut','CutControls'),
                       ('joint-copy','NonauthorConsumer\nimport Controls\nimport CutControls')]:
        p=HERE/folder
        text='''import TOP
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some c := env.find? `Universal233.CoreProgram.generate.eq_1 | throwError "missing declaration"
  logInfo m!"DECL_TYPE|{repr c.type}"
  match c with
  | .thmInfo t => logInfo m!"DECL_VALUE|{repr t.value}"
  | _ => throwError "expected theorem"
'''.replace('TOP',top)
        (p/'FreshOriginCollision.lean').write_text(text);r=run(p,'FreshOriginCollision');assert not r['exit']
        content=(p/'FreshOriginCollision.log').read_text()
        reports.append({'build':r,'folder':folder,'type_and_value_sha256':digest(p/'FreshOriginCollision.log')})
    assert len({r['type_and_value_sha256'] for r in reports})==1,reports
    report={'declaration':'Universal233.CoreProgram.generate.eq_1',
      'origins':{'isolated-source':'Entrypoint','isolated-cut':'InitialCoverage','joint-copy':'InitialCoverage'},
      'cause':'equation theorem generated lazily at first unfolding; both sources contain same named declaration',
      'exact_raw_Expr_type_and_proof_body_identical':True,'reports':reports}
    (ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-origin-collision-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS_GENERATED_ORIGIN_COLLISION',reports[0]['type_and_value_sha256'])

if __name__=='__main__':main()
