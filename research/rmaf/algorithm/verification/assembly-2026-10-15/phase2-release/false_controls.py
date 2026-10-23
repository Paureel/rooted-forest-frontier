"""Explicit false candidate propositions, paired with actual clean twins."""
import json
from rebuild import ROOT,HERE,run,digest
from readout import C,tree,lit,vertex,req

def main():
    b=HERE/'isolated-completion';H=C['hard_parent'];M=C['macros'][0];E=C['clearing_not_final_agreement']
    text='''import HardPaid
open RMAF Universal233 CoreProgram SourceCoverage VertexGeometry
def refinesB (F Q : List (List Nat)) : Bool := F.all (fun p => Q.any (fun q => p.all q.contains))
'''
    text+=f'def hardSource : Tree := {tree(H["source"])}\ndef hardTarget : Tree := {tree(H["target"])}\n'
    for j,m in enumerate(C['macros']):
        fn=['cliqueOutputs','fourChainOutputs','diagonalOutputs'][j]
        text+=f'def S{j} : Tree := {tree(m["source"])}\ndef T{j} : Tree := {tree(m["target"])}\n'
        args=vertex(m['v'])+(' '+vertex(m['w']) if 'w' in m else '')
        text+=f'def os{j} (q : Nat) := WholeSourceMass.{fn} S{j} T{j} {lit(m["parents"][0])} {lit(m["parents"][1])} {args} q\n'
    args=' '.join(req(m,E) for m in E['modes'])
    text+=f'def badS : Tree := {tree(E["source"])}\ndef badT : Tree := {tree(E["target"])}\n'
    text+=f'def badQ : Output := ((generate badS (Assembly.requestedColor badT {lit(E["parents"][0])} {lit(E["parents"][1])} {args}) 6).outputs).getD 0 ⟨[],[]⟩\n'
    text+='def duplicateClique := os0 4 ++ [(os0 4).getD 0 ⟨[],[]⟩]\n'
    text+='theorem trueMass2 : rawQMass 2 (os0 4) = mkRat 3 16 := by decide +kernel\n'
    text+='theorem trueMass233 : rawQMass (233/100) (os0 4) = mkRat 300000000 2947295521 := by decide +kernel\n'
    text+='theorem trueDuplicateMass2 : rawQMass 2 duplicateClique = mkRat 1 4 := by decide +kernel\n'
    cross=lit(json.loads((HERE.parent/'CONTROL-ADDENDUM-v1.json').read_text())['proper_but_crossing_source_parents']['parents'])
    cases=[
      ('EndpointIgnored','refinesB [[0,2,3],[1]] (HardParent.literalThree hardSource [false,false,true] [false,true]) = true',
       'refinesB [[0,2,3],[1]] (HardParent.literalThree hardSource [false,false,true] [false,true]) = false',''),
      ('ReverseCoverage','refinesB [[0,1],[2]] [[0],[1],[2]] = true','refinesB [[0],[1],[2]] [[0,1],[2]] = true',''),
      ('ClearingAlreadyAgreement','agreement badT badS badQ.partition = true','agreement badT badS badQ.partition = false',''),
      ('CliqueOmission','(os0 4).length = 2','(os0 4).length = 3',''),
      ('FourOmission','(os1 4).length = 3','(os1 4).length = 4',''),
      ('DiagonalUnpaid','(os2 4).map (fun o => o.sourceCuts.length) = [3,3]','(os2 4).map (fun o => o.sourceCuts.length) = [3,4]',''),
      ('ExtraHardCuts','(os0 4).map (fun o => o.sourceCuts.length) = [6,6,6]','(os0 4).map (fun o => o.sourceCuts.length) = [4,4,4]',''),
      ('DroppedDuplicate','duplicateClique.length = 3','duplicateClique.length = 4',''),
      ('RootThirdRegion','(regions [0,1] (.node (.leaf 0) (.leaf 1)) []).length = 3','(regions [0,1] (.node (.leaf 0) (.leaf 1)) []).length = 2',''),
      ('SelectedLeafCleared','(minimalVertices [0] (.node (.leaf 0) (.leaf 1))).contains [false] = false','(minimalVertices [0] (.node (.leaf 0) (.leaf 1))).contains [false] = true',''),
      ('SourceCrossing',f'pairwiseEmbeddings S0 {cross} = true',f'pairwiseEmbeddings S0 {cross} = false',''),
      ('BudgetPruning','(os2 3).length = 2','(os2 3).length = 1',''),
      ('ExtraDiscountMass2','rawQMass 2 (os0 4) ≤ mkRat 3 64','rawQMass 2 (os0 4) = mkRat 3 16','rw [trueMass2]\n  '),
      ('MissingDuplicateMass2','rawQMass 2 duplicateClique = mkRat 3 16','rawQMass 2 duplicateClique = mkRat 1 4','rw [trueDuplicateMass2]\n  ')]
    old=json.loads((ROOT/'research/rmaf/results/algorithm-assembly-prerelease-review-addendum-v1.json').read_text())
    wrong=next(r['wrong_rhs'] for r in old['negative'] if r['id']=='clique-false-extra-discount-inequality' and r['c']==[233,100])
    cases.append(('ExtraDiscountMass233',f'rawQMass (233/100) (os0 4) ≤ mkRat {wrong[0]} {wrong[1]}',
      'rawQMass (233/100) (os0 4) = mkRat 300000000 2947295521','rw [trueMass233]\n  '))
    positive=text+'\n'+''.join(f'theorem clean{i} : {good} := by decide +kernel\n' for i,(_,bad,good,tac) in enumerate(cases))
    (b/'FreshCleanControls.lean').write_text(positive);clean=run(b,'FreshCleanControls');assert not clean['exit'],clean
    records=[]
    for name,bad,good,tac in cases:
        m='False'+name;(b/(m+'.lean')).write_text(text+f'\nexample : {bad} := by\n  {tac}decide\n')
        r=run(b,m);s=(b/(m+'.log')).read_text()
        ok=r['exit']!=0 and 'proved that the proposition' in s and 'is false' in s and 'failed to reduce' not in s
        records.append({**r,'source_sha256':digest(b/(m+'.lean')),'intended_false_proposition':bad,'rejected_for_false_proposition':ok})
        report={'status':'IN_PROGRESS','positive_build':clean,'records':records,'expected_negative_count':len(cases)}
        out=ROOT/'research/rmaf/results/algorithm-assembly-fresh-review-false-controls-v1.json';out.write_text(json.dumps(report,indent=2)+'\n')
        assert ok,(m,s)
    report.update({'status':'PASS_EXPLICIT_FALSE_PROPOSITION_CONTROLS','positive_twin_count':len(cases),
                   'actual_false_proposition_count':len(cases),'no_inconclusive_reduction_counted':True,
                   'replication_count_added':0,'all_main_milestones':'OPEN'})
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],len(cases),'actual false propositions; matching clean twins pass')

if __name__=='__main__':main()
