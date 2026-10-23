#!/usr/bin/env python3
"""Build the actual extractor minimal-embedding interface in a fresh import directory.

Driver/diagnostic-parser lineage: adapted from executable/audit.py. This is a
kernel and source-integrity audit, not an independent mathematical reference.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
RUN = BASE / 'audit' / time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
DEPS = RUN / 'deps'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
AXIOMS = re.compile(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])", re.S)

def rel(p): return str(p.relative_to(ROOT))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def explicit_false(code, log):
    return code != 0 and log.count(': error:') == 1 and re.search(
        r'error: Tactic `decide` proved that the proposition\n[\s\S]+?\nis false(?:\n|$)', log) is not None

def main():
    DEPS.mkdir(parents=True, exist_ok=False)
    started=time.perf_counter()
    env=os.environ.copy(); env['LEAN_PATH']=str(DEPS)
    r={'status':'pending', 'scope':'Actual unchanged minimalVertices realizes MinimalEmbedding with actual ambient and selected-occurrence semantics, universal leastness, and original region consumer.',
       'not_established':['cross-tree restriction/suppression transport','G2–G7','complete pure-bridge exchange','safe cover','unrestricted runtime bound','novelty'],
       'run_directory':rel(RUN),'source_hashes':{},'builds':{},'axioms':{},'false_controls':{},'parser_controls':{}}
    control=json.loads((BASE/'audit-controls.json').read_text())
    for c in control['planted_diagnostics']:
        actual=explicit_false(c['exit'],c['message']); assert actual==c['accepted'],c['name']
        r['parser_controls'][c['name']]={'expected':c['accepted'],'actual':actual}
    modules=[
        ('RMAF',ROOT/'research/rmaf/lean/RMAF.lean'),
        ('PureBridge',ROOT/'research/rmaf/pure_bridge/lean/PureBridge.lean'),
        ('GraphRegion',ROOT/'research/rmaf/bridge_review/lean/GraphRegion.lean'),
        ('ExecutableConnectivity',ROOT/'research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean'),
        ('TreeAddresses',BASE/'address_semantics/TreeAddresses.lean'),
        ('ExtractorLeastness',BASE/'lean/ExtractorLeastness.lean'),
        ('ActualEmbedding',BASE/'lean/ActualEmbedding.lean'),
        ('LeastnessControls',BASE/'lean/LeastnessControls.lean')]
    new_modules=modules[-4:]
    false=sorted((BASE/'lean/negative').glob('*.lean'))
    malformed=BASE/'lean/malformed/WrongType.lean'; twin=BASE/'lean/CleanTwin.lean'
    sources=[p for _,p in modules]+false+[malformed,twin,BASE/'audit.py',BASE/'CONTROLS.json',BASE/'audit-controls.json']
    r['source_hashes']={rel(p):sha(p) for p in sources}
    assert sha(BASE/'CONTROLS.json')==(BASE/'controls.sha256').read_text().split()[0]
    r['frozen_control_hash_matched']=True
    expected=[]; counts={}
    for module,p in modules:
        s=p.read_text()
        assert not re.search(r'^\s*(axiom|opaque|unsafe)\b|\b(sorry|admit|native_decide)\b',s,re.M),rel(p)
        if (module,p) in new_modules:
            ns='LeastEmbedding.Controls' if module=='LeastnessControls' else 'LeastEmbedding'
            declarations=re.findall(r'^theorem\s+(\S+)',s,re.M)
            defs=re.findall(r'^def\s+(\S+)',s,re.M)
            expected.extend(ns+'.'+n for n in declarations+defs)
            counts[module]={'theorems':len(declarations),'definitions':len(defs)}
    audit_source=RUN/'AxiomAudit.lean'
    audit_source.write_text('import LeastnessControls\n'+'\n'.join('#print axioms '+n for n in expected)+'\n')
    r['source_hashes'][rel(audit_source)]=sha(audit_source)
    def execute(name,path,out=None):
        cmd=[str(ROOT/'bootloops-lean')]
        if out is not None:cmd+=['-o',str(out)]
        cmd.append(str(path));t=time.perf_counter()
        result=subprocess.run(cmd,cwd=ROOT,env=env,text=True,capture_output=True,timeout=60)
        log=result.stdout+result.stderr;p=RUN/(name+'.log');p.write_text(log)
        record={'exit_code':result.returncode,'seconds':time.perf_counter()-t,'log':rel(p),'log_sha256':sha(p)}
        return result.returncode,log,record
    version=subprocess.run([str(ROOT/'bootloops-lean'),'--version'],cwd=ROOT,env=env,text=True,capture_output=True,check=True,timeout=60)
    r['lean_version']=version.stdout.strip();(RUN/'version.log').write_text(version.stdout+version.stderr)
    for name,p in modules:
        code,log,record=execute(name,p,DEPS/(name+'.olean'))
        assert code==0 and ': error:' not in log and 'sorryAx' not in log,(name,log)
        r['builds'][name]=record
    code,log,record=execute('AxiomAudit',audit_source)
    assert code==0 and ': error:' not in log and 'sorryAx' not in log,log
    for name,body in AXIOMS.findall(log):
        axioms=[] if body.startswith('does not') else [x.strip() for x in body.split('[',1)[1].rstrip(']').split(',')]
        assert set(axioms)<=ALLOWED,(name,axioms)
        assert name not in r['axioms'],name
        r['axioms'][name]=axioms
    assert set(r['axioms'])==set(expected),(set(expected)-set(r['axioms']),set(r['axioms'])-set(expected))
    r['builds']['AxiomAudit']=record
    for p in false:
        code,log,record=execute(p.stem,p)
        assert explicit_false(code,log),(p.name,log)
        record.update(rejected_as_false=True,positive_twin=control['true_twins'][p.stem]);r['false_controls'][p.stem]=record
    code,log,record=execute('MalformedWrongType',malformed)
    assert code!=0 and 'Type mismatch' in log and not explicit_false(code,log),log
    record['rejected_as_falsity_receipt']=True;r['malformed_diagnostic_control']=record
    code,log,record=execute('CleanTwin',twin)
    assert code==0 and ': error:' not in log,log
    r['clean_diagnostic_twin']=record
    for p in sources+[audit_source]:assert r['source_hashes'][rel(p)]==sha(p),rel(p)
    r['module_counts']=counts;r['new_theorem_count']=sum(c['theorems'] for c in counts.values())
    r['new_definition_count']=sum(c['definitions'] for c in counts.values())
    r['new_axiom_report_count']=len(r['axioms']);r['seconds']=time.perf_counter()-started
    r['status']='kernel-checked-actual-minimal-embedding';r['semantic_review']='separate, pending at audit creation'
    output=json.dumps(r,indent=2)+'\n'
    (RUN/'certificate.json').write_text(output);(BASE/'audit/certificate.json').write_text(output)
    (ROOT/'research/rmaf/results/bridge-leastness-lean.json').write_text(output)
    print(json.dumps({'status':r['status'],'new_theorems':r['new_theorem_count'],'axiom_reports':len(r['axioms']),'false_controls':len(r['false_controls']),'malformed_control_rejected':True,'seconds':r['seconds']}))

if __name__=='__main__':main()
