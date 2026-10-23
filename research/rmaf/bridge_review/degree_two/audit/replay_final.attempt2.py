"""Source-bound author replay. Independent semantic review is separate.
Run: ./bootloops-python research/rmaf/bridge_review/degree_two/replay_final.py
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, time
ROOT=Path('research/rmaf/bridge_review/degree_two')
DEPENDENCIES=[
('RMAF','research/rmaf/lean/RMAF.lean','4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9'),
('PureBridge','research/rmaf/pure_bridge/lean/PureBridge.lean','acf08329466b6449c39c5edb0914c7af15f30690b25b8f0389cb65b2b24943f4'),
('GraphRegion','research/rmaf/bridge_review/lean/GraphRegion.lean','5d53cadd43f7c654656040218939c2051f8592e5045227bc2506dd2cddee5455'),
('ExecutableConnectivity','research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean','63044b33c7ff23cad5ec4886035ff112acb9bb42a18dd479090c4d3a638f311f'),
('TreeAddresses','research/rmaf/bridge_review/leastness/address_semantics/TreeAddresses.lean','f2bbd08201b98893a0e824f041e9af72761933d7f29b4e9a89088d9d9e46fdb0'),
('ExtractorLeastness','research/rmaf/bridge_review/leastness/lean/ExtractorLeastness.lean','8626d726a1635b06c9f58178dbb8a84cecdb55630eb138a5afc8353618b4f1b8'),
('ActualEmbedding','research/rmaf/bridge_review/leastness/lean/ActualEmbedding.lean','8c10ef67cec9ef067e3bf2a104c342e1d536a07546d05ffc759e6b3ded3d69a4')]
NEW=[
('DegreePropagation','graph_route/lean/DegreePropagation.lean','DegreeTwoGraph'),
('GraphRouteControls','graph_route/lean/GraphRouteControls.lean','DegreeTwoGraphControls'),
('DegreePropagationControls','graph_route/lean/DegreePropagationControls.lean','DegreeTwoGraphControls'),
('PartitionRefinement','lean/PartitionRefinement.lean','DegreeTwo'),
('ConsumerControls','lean/ConsumerControls.lean','DegreeTwo.ConsumerControls'),
('LocalSplit','lean/LocalSplit.lean','DegreeTwo'),
('DegreeCounting','lean/DegreeCounting.lean','DegreeTwo'),
('LocalSplitControls','lean/LocalSplitControls.lean','DegreeTwo.LocalControls'),
('AgreementBlock','lean/AgreementBlock.lean','DegreeTwo'),
('RestrictionTransport','restriction_route/RestrictionTransport.lean','RestrictionRoute'),
('SupportAlgebra','restriction_route/SupportAlgebra.lean','RestrictionRoute'),
('SupportProfile','restriction_route/SupportProfile.lean','RestrictionRoute'),
('ActualSupportTransport','restriction_route/ActualSupportTransport.lean','RestrictionRoute'),
('Controls','restriction_route/Controls.lean','RestrictionRouteControls'),
('TransportUseSites','restriction_route/TransportUseSites.lean','RestrictionRouteUseSites'),
('ActualRefinement','lean/ActualRefinement.lean','DegreeTwo'),
('RefinementControls','lean/RefinementControls.lean','DegreeTwo.RefinementControls')]

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(s):
    # These audited modules use ordinary block/line comments, without nested blocks.
    return re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)

def main():
    runid=time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())
    out=ROOT/'replay'/runid;out.mkdir(parents=True,exist_ok=False)
    build=out/'build';build.mkdir()
    env=os.environ.copy();env['LEAN_PATH']=str(build)
    pins={};rows=[];decls=[]
    for name,path,pin in DEPENDENCIES:
        p=Path(path);assert sha(p)==pin,(path,'completed source drift');pins[path]=pin
    for name,rel,ns in NEW:
        p=ROOT/rel;text=p.read_text();pins[str(p)]=sha(p)
        code=strip_comments(text)
        assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^\s*axiom\s',code,re.M),(p,'forbidden proof escape')
        for kind,n in re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?(theorem|def|abbrev|structure)\s+(\w+)',code,re.M):
            decls.append(dict(name=ns+'.'+n,kind=kind,module=name,source=str(p),sha256=sha(p)))
    def run_lean(name,p,args=(),expected=0,explicit_false=False):
        started=time.monotonic();q=subprocess.run(['./bootloops-lean',*args,str(p)],env=env,capture_output=True,text=True)
        log=out/(name+'.log');log.write_text(q.stdout+q.stderr)
        row=dict(name=name,source=str(p),source_sha256=sha(p),exit_code=q.returncode,
                 seconds=time.monotonic()-started,log=str(log),log_sha256=sha(log),expected_exit=expected)
        if explicit_false:
            row['explicit_false']=bool(re.search(r'by decide.*is false',log.read_text(),re.S))
            assert q.returncode!=0 and row['explicit_false'],(name,log.read_text())
            assert not re.search(r'unknown module|unknown constant|unknown identifier|type mismatch',log.read_text(),re.I),(name,'diagnostic failure is not semantic falsity')
        else:assert q.returncode==expected,(name,log.read_text())
        rows.append(row)
    for name,path,pin in DEPENDENCIES:run_lean(name,Path(path),('-o',str(build/(name+'.olean'))))
    for name,rel,ns in NEW:run_lean(name,ROOT/rel,('-o',str(build/(name+'.olean'))))
    ax=out/'AllAxioms.lean';ax.write_text('\n'.join('import '+n for n,_,_ in NEW)+'\n\n'+'\n'.join('#print axioms '+d['name'] for d in decls)+'\n')
    run_lean('AllAxioms',ax)
    reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",(out/'AllAxioms.log').read_text())
    assert len(reports)==len(decls),(len(reports),len(decls))
    assert {n for n,_ in reports}=={d['name'] for d in decls}
    allowed={'propext','Classical.choice','Quot.sound'}
    for n,a in reports:assert {x.strip() for x in a.split(',') if x.strip()}<=allowed,(n,a)
    for p in sorted((ROOT/'graph_route/lean/negative').glob('*.lean')):run_lean('graph-'+p.stem,p,expected=1,explicit_false=True)
    for p in sorted((ROOT/'lean/negative').glob('*.lean')):run_lean('parent-'+p.stem,p,expected=1,explicit_false=True)
    for n in ['wrong-degree','missing-path','wrong-root','cross-address','overlap','wrong-cost','repeated-labels']:
        run_lean('restriction-'+n,ROOT/'restriction_route'/(n+'.lean'),expected=1,explicit_false=True)
    run_lean('Malformed',ROOT/'lean/malformed/WrongType.lean',expected=1)
    assert 'Type mismatch' in (out/'Malformed.log').read_text()
    assert 'by decide' not in (out/'Malformed.log').read_text()
    run_lean('CleanTwin',ROOT/'lean/CleanTwin.lean')
    for path,pin in pins.items():assert sha(Path(path))==pin,(path,'source changed during replay')
    (out/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
    receipt=dict(status='passed-author-replay-fresh-review-pending',scope='Actual degree-two local refinement and original agreement-partition consumer; no full ExchangeSystem realization.',
        source_pins=pins,declarations=decls,axiom_reports=len(reports),standard_axioms_only=True,
        builds_and_controls=rows,script=str(Path(__file__).relative_to(Path.cwd())),script_sha256=sha(Path(__file__)),
        unique_named_theorems=sum(d['kind']=='theorem' for d in decls),definitions=sum(d['kind'] in ['def','abbrev'] for d in decls),structures=sum(d['kind']=='structure' for d in decls),
        negative_controls=sum(bool(x.get('explicit_false')) for x in rows),
        lineage='Shared actual definitions and Lean kernel; author replay. Graph and restriction routes separately pinned; independent nonauthor semantic review is mandatory and recorded separately.')
    rec=out/'receipt.json';rec.write_text(json.dumps(receipt,indent=2)+'\n')
    (ROOT/'FINAL-REPLAY.json').write_text(json.dumps(dict(receipt=str(rec),sha256=sha(rec),status=receipt['status']),indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','axiom_reports','unique_named_theorems','definitions','structures','negative_controls']}))

if __name__=='__main__':main()
