#!/usr/bin/env python3
"""Replay this route's Std-only Lean build, axiom inventory and false controls.
Problem-specific audit adapter; preserves failure logs and fails closed.
"""
import hashlib, json, os, re, subprocess, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
AUDIT=HERE/'audit'
EXPECTED=['deepest_root_in_neighbor','deepest_neighbors_intersect','at_most_one_occupant','avoids_weaken','ExchangeSystem.free_replacement','ExchangeSystem.paid_replacement','ExchangeSystem.paid_minimum','ExchangeSystem.free_minimum','one_cut_query_dichotomy','role_swap_parameter','role_swap_minimum','bounded_second_query','negative_budget_impossible','Controls.bad_repair_optimum','Controls.bad_repair_forced_keeper','Controls.one_unit_repair_rejected']
EXPECTED_MARKS=['proper_labels','vertex_marks_have_degree_two','marks_are_unlabelled','exact_four_optima','joint_mark_witness','every_feasible_at_least','every_joint_mark_forest_costs_two','separate_zero_penalties_do_not_compose']
ALLOWED={'propext','Classical.choice','Quot.sound'}

def run(args,log):
    start=time.monotonic(); p=subprocess.run(args,cwd=HERE,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env={**os.environ,'ELAN_HOME':str(ROOT/'.runtime/elan')},timeout=60)
    (AUDIT/log).write_text(p.stdout)
    return p,time.monotonic()-start

def main():
    AUDIT.mkdir(exist_ok=True)
    source=(HERE/'PureBridge.lean').read_text()+(HERE/'MarkInteraction.lean').read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b',source,re.M),'disallowed declaration or proof shortcut'
    version,_=run([str(ROOT/'bootloops-lean'),'--version'],'version.log');assert version.returncode==0 and 'version 4.35.0' in version.stdout
    build,buildsecs=run([str(ROOT/'bootloops-lake'),'build'],'build.log');assert build.returncode==0,'Lean build failed'
    check,checksecs=run([str(ROOT/'bootloops-lean'),'PureBridge.lean'],'axioms.log');assert check.returncode==0,'axiom replay failed'
    markcheck,marksecs=run([str(ROOT/'bootloops-lake'),'env','lean','MarkInteraction.lean'],'axioms-marks.log');assert markcheck.returncode==0,'mark axiom replay failed'
    combined=check.stdout+markcheck.stdout
    axioms={}
    for full in ['PureBridge.'+name for name in EXPECTED]+['PureBridgeMarks.'+name for name in EXPECTED_MARKS]:
        if "'"+full+"' does not depend on any axioms" in combined:deps=[]
        else:
            m=re.search(re.escape("'"+full+"' depends on axioms: [")+r'([^\]]*)\]',combined)
            assert m,'missing axiom report: '+full
            deps=[x.strip() for x in m.group(1).split(',') if x.strip()]
        assert set(deps)<=ALLOWED,(full,deps)
        axioms[full]=deps
    negatives={}
    for stem in ['FalseRepair','FalseDepth','FalseJointPenalty']:
        p,seconds=run([str(ROOT/'bootloops-lake'),'env','lean','negative/'+stem+'.lean'],'negative-'+stem+'.log')
        assert p.returncode!=0,stem+' false control unexpectedly succeeded'
        assert 'Tactic `decide` proved that the proposition' in p.stdout and 'is false' in p.stdout,stem+' did not fail as a false proposition'
        assert 'unknown module' not in p.stdout and 'unknown identifier' not in p.stdout,stem+' failed for infrastructure reason'
        negatives[stem]={'rejected':True,'exit_code':p.returncode,'seconds':seconds}
    files=['PureBridge.lean','MarkInteraction.lean','negative/FalseRepair.lean','negative/FalseDepth.lean','negative/FalseJointPenalty.lean','audit.py','../../lean/RMAF.lean']
    cert={'status':'kernel-checked-conditional-interface','lean_version':version.stdout.strip(),'theorem_count':len(axioms),'axioms':axioms,'negative_controls':negatives,'source_hashes':{f:hashlib.sha256((HERE/f).read_bytes()).hexdigest() for f in files},'build_seconds':buildsecs,'axiom_replay_seconds':checksecs,'mark_axiom_replay_seconds':marksecs,'scope':'Std-only abstract exchange and rooted-region lemmas; a separate finite degree-two mark counterexample imports the existing RMAF executable model and shares its semantic lineage. Minimal embeddings, split transport, region partition equivalence and graph realization remain unproved; no unrestricted rMAF bound certified.'}
    (AUDIT/'certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps({'status':cert['status'],'theorem_count':len(axioms),'negative_controls':negatives,'build_seconds':buildsecs,'axiom_replay_seconds':checksecs}))

if __name__=='__main__':main()
