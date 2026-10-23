#!/usr/bin/env python3
"""One-shot source, axiom and exact-diagnostic audit of the fresh build.
Only successful final logs may contribute acceptance; failed reviewer drafts remain archived.
"""
import hashlib,json,os,re,subprocess,time
from pathlib import Path
from rebuild import ROOT,HERE,BUILD,SOURCES,digest

def lean(name,source):
    path=BUILD/(name+'.lean'); path.write_text(source)
    env=os.environ.copy(); env['LEAN_PATH']=str(BUILD)
    before=time.monotonic()
    p=subprocess.run([str(ROOT/'bootloops-lean'),str(path)],cwd=BUILD,env=env,capture_output=True,text=True,timeout=60)
    output=p.stdout+p.stderr
    (HERE/(name+'.log')).write_text(output)
    return dict(name=name,exit_code=p.returncode,seconds=time.monotonic()-before,source_sha256=digest(path)),output

def run():
    manifest=json.loads((HERE/'source-manifest.json').read_text())
    parity=[]; names=[]; forbidden=[]
    for record in manifest:
        module=record['module']; p=Path(record['source']); snap=Path(record['snapshot'])
        assert digest(p)==digest(snap)==record['sha256']
        parity.append(dict(module=module,original=snap.read_bytes()==p.read_bytes(),sha256=digest(p)))
        text=snap.read_text()
        forbidden += [(module,m.group()) for m in re.finditer(r'\b(sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by|extern)\b',text)]
        namespaces=[]
        for line in text.splitlines():
            m=re.match(r'^namespace\s+(\S+)',line)
            if m:namespaces.append(m[1]);continue
            m=re.match(r'^end\s+(\S+)',line)
            if m:
                assert namespaces.pop()==m[1]
                continue
            m=re.match(r'^(?:noncomputable\s+)?(?:def|theorem|abbrev)\s+([\w.]+)',line)
            if m:names.append('.'.join(namespaces+[m[1]]))
    assert not forbidden,forbidden
    historical=[]
    old=ROOT/'research/rmaf/bridge_review/executable/fresh_review/build'
    for module in ('RMAF','PureBridge','GraphRegion','ExecutableConnectivity'):
        before=old/(module+'.lean'); now=BUILD/(module+'.lean')
        assert before.exists()
        same=before.read_bytes()==now.read_bytes()
        assert same,module
        historical.append(dict(module=module,previous_snapshot=str(before),same=same,sha256=digest(now)))
    row,output=lean('AxiomReview','import ActualEmbedding\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
    assert row['exit_code']==0,output
    reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",output)
    assert len(reports)==len(names),(len(reports),len(names))
    axioms=set()
    for _,values in reports:
        axioms.update(v.strip() for v in values.split(',') if v.strip())
    assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
    prefix='import ReviewerChecks\nopen RMAF LeastEmbedding FreshLeastnessReview\n'
    bads={
      'FalseExtraRoot':'example : ([] : Vertex) ∈ minimalVertices [0,1] quartet := by decide\n',
      'FalseDeletedPath':'example : minimalVertices [0,2] quartet = [[],[false,false],[true],[true,false]] := by decide\n',
      'FalseCollapsedOccurrence':'example : terminals [0] repeated = [[false]] := by decide\n',
      'FalseInvalidAmbient':'example : [false,false,false] ∈ vertices quartet := by decide\n',
      'FalseMissingTerminal':'example : ([false,true] : Vertex) ∈ [[false],[false,false]] := by decide\n',
      'FalseDuplicateSelection':'example : minimalVertices [0,0] quartet = [[],[false],[false,false]] := by decide\n'}
    negatives=[]
    for name,body in bads.items():
        row,output=lean(name,prefix+body)
        row['exact_false']=('decide' in output and 'proposition' in output and 'is false' in output)
        assert row['exit_code']!=0 and row['exact_false'],output
        assert 'Unknown identifier' not in output and 'failed to synthesize' not in output,output
        negatives.append(row)
    malformed,out=lean('MalformedTrue',prefix+'example : True := by exact unavailableFreshProof\n')
    assert malformed['exit_code']!=0 and 'Unknown identifier' in out,out
    malformed['classification']='diagnostic-only, excluded from semantic rejection count'
    twin,out=lean('CleanTrue',prefix+'example : True := by trivial\n')
    assert twin['exit_code']==0,out
    receipt=dict(status='PASS',source_parity=parity,unchanged_checkpoint=historical,
        forbidden_tokens=forbidden,axiom_review=row,axiom_report_count=len(reports),axioms=sorted(axioms),
        false_rejections=negatives,malformed=malformed,clean_twin=twin,
        excluded_review_draft='ReviewerChecks-attempt1.lean/.log (elaboration failed; no acceptance credit)')
    (HERE/'source-audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('status','axiom_report_count','axioms','forbidden_tokens')}))
    print(json.dumps(dict(exact_false_rejections=len(negatives),malformed_excluded=True,source_parity=len(parity))))
if __name__=='__main__':run()
