"""Independent source-only builds of the four released packages.

Reuses this reviewer's immutable prior compiler/origin-log primitives only;
no author Python replay code is imported. All package membership/import maps
and copy-only adaptations are independently checked here.
"""
from pathlib import Path
import os,sys,json,hashlib,importlib.util,re
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[6];HERE=Path(__file__).resolve().parent
OLD=ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/phase2-release/rebuild.py'
spec=importlib.util.spec_from_file_location('own_frozen_compiler',OLD)
H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
digest=H.digest;run=H.run;audit_text=H.audit_text;parse_audit=H.parse_audit

CERTS={
 'assembly':'research/rmaf/algorithm/universal233/assembly/replay/20261015T084051Z/certificate.json',
 'mass':'results/algorithm-universal233-whole-mass-20261015T082345Z/certificate.json',
 'hard':'results/algorithm-universal233-hard-refinement-20261015T084225Z/certificate.json',
 'completion':'results/algorithm-universal233-assembly-completion-20261015T090155Z/certificate.json'}

def sources(arm):
    d=json.loads((ROOT/CERTS[arm]).read_text());rows=[]
    if arm in ['assembly','completion']:
        order=d['positive_order']
        for r in d['source_inputs']:
            row={'module':r.get('compiled_module',r['module']),'source':r['source'],
                 'source_sha256':r.get('source_sha256',r.get('sha256')),
                 'compiled_sha256':r.get('compiled_sha256',r.get('sha256')),
                 'adapter':r.get('adapter')}
            rows.append(row)
    else:
        order=list(d['module_origin_counts']) if arm=='mass' else [r['module'] for r in d['builds']][:26]
        pins=d['input_hashes'] if arm=='mass' else d['hashes']
        by_name={Path(p).stem:(p,h) for p,h in pins.items() if p.endswith('.lean')}
        for m in order:
            p,h=by_name[m];rows.append({'module':m,'source':p,'source_sha256':h,'compiled_sha256':h,'adapter':None})
    # Assembly records both upstream source stacks, including shared modules.
    # Retain every contact/pin, then collapse only byte-identical compiled
    # module claims to the explicit positive order.
    by_module={}
    for r in rows:
        if r['module'] in by_module:
            assert r['compiled_sha256']==by_module[r['module']]['compiled_sha256'],r
            assert digest(ROOT/r['source'])==r['source_sha256'],r
            by_module[r['module']].setdefault('equivalent_source_contacts',[]).append(r)
        else:by_module[r['module']]=r
    assert set(by_module)==set(order)
    rows=[by_module[m] for m in order]
    return d,order,rows

def main():
    arm=sys.argv[1];cert,order,rows=sources(arm);build=HERE/('isolated-'+arm);build.mkdir(exist_ok=False)
    for r in rows:
        p=ROOT/r['source'];assert digest(p)==r['source_sha256'],p
        data=p.read_bytes();original=data
        if r['adapter']:
            if r['module']=='CutCoverage':assert r['adapter']=='module filename only Coverage -> CutCoverage'
            elif r['module']=='InitialCoverage':
                assert data.startswith(b'import Coverage\n');data=data.replace(b'import Coverage\n',b'import CutCoverage\n',1)
                assert data.split(b'\n',1)[1]==original.split(b'\n',1)[1]
            else:raise AssertionError('unlicensed adapter '+repr(r))
        out=build/(r['module']+'.lean');out.write_bytes(data)
        assert digest(out)==r['compiled_sha256'],r
        r.update({'realpath':str(p.resolve()),'copy':str(out.relative_to(ROOT)),
                  'whole_source_unchanged':data==original,
                  'all_theorem_body_bytes_unchanged':data.split(b'\n',1)[1]==original.split(b'\n',1)[1]})
    imports=[]
    for r in rows:
        text=(build/(r['module']+'.lean')).read_text()
        for group in re.findall(r'^import\s+([^\n]+)',text,re.M):
            for m in group.split():
                assert m in order or m in ['Std','Lean'],(r['module'],m,'unregistered import')
                imports.append({'from':r['module'],'import':m,'project':m in order})
    result={'arm':arm,'source_inputs':rows,'imports':imports,'builds':[],
      'membership_certificate':CERTS[arm],'certificate_sha256':digest(ROOT/CERTS[arm]),
      'reused_own_compiler_helper':str(OLD.relative_to(ROOT)),'helper_sha256':digest(OLD),
      'no_author_python_imports':True,'copied_olean_files':0}
    dest=ROOT/f'research/rmaf/results/algorithm-assembly-fresh-review-{arm}-rebuild-v1.json'
    for m in order:
        r=run(build,m,['-o',m+'.olean']);result['builds'].append(r)
        dest.write_text(json.dumps(result,indent=2)+'\n');print(arm,m,r['exit'],round(r['seconds'],3),flush=True)
        if r['exit']:raise SystemExit(1)
    (build/'FreshAudit.lean').write_text(audit_text(order,'\nimport '.join(order)))
    a=run(build,'FreshAudit');result['builds'].append(a)
    dest.write_text(json.dumps(result,indent=2)+'\n');assert not a['exit'],a
    result['audit']=parse_audit(build/'FreshAudit.log',order);assert not result['audit']['forbidden']
    expected=cert.get('module_counts',cert.get('module_origin_counts'))
    assert result['audit']['counts']==expected,(result['audit']['counts'],expected)
    result['all_source_pins_unchanged']=all(digest(ROOT/r['source'])==r['source_sha256'] for r in rows)
    result['olean_sha256']={m:digest(build/(m+'.olean')) for m in order}
    result['status']='PASS_INDEPENDENT_ISOLATED_REBUILD_FULL_ORIGIN'
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print('AUDIT',arm,result['audit']['total'],result['audit']['axiom_union'],flush=True)

if __name__=='__main__':main()
