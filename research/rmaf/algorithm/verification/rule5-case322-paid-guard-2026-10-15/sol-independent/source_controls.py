"""One-shot exact source/import-adaptation controls, fresh own Std-only bytes.
An explicit allowed import substitution is tested; no candidate source contact.
"""
import copy, hashlib, json, pathlib, time, traceback
import producer_controls as pc
H=pathlib.Path(__file__).resolve().parent;D=H/'adaptation-controls'
ORIGINAL='import Case322Dep\nnamespace Case322Adapt\ntheorem token : True := Case322Same.token\nend Case322Adapt\n'
IMPORTS={'Case322Dep':'Case322CleanA'}
def sha(b):return hashlib.sha256(b).hexdigest()
def adapt(text,mapping):
    return ''.join('import '+mapping.get(line.strip()[7:],line.strip()[7:])+'\n'if line.startswith('import ')else line for line in text.splitlines(keepends=True))
def validate(rows,expected):
    if rows!=expected:raise ValueError('SOURCE_MAPPING_IDENTITY')
    if len(rows)!=1 or len({r['adapted_path']for r in rows})!=1:raise ValueError('SOURCE_MAPPING_DENOMINATOR')
    for r in rows:
        original=pathlib.Path(r['original_path']).read_bytes();adapted=pathlib.Path(r['adapted_path']).read_bytes()
        if sha(original)!=r['original_sha256']or sha(adapted)!=r['adapted_sha256']:raise ValueError('SOURCE_BYTES')
        if adapt(original.decode(),r['import_map']).encode()!=adapted:raise ValueError('IMPORT_ADAPTATION')
    return True
def check(name,ok,checks):
    checks.append(dict(name=name,passed=bool(ok)))
    if not ok:raise AssertionError(name)
def main():
    start=time.perf_counter();D.mkdir(exist_ok=True);original=D/'OriginalControl.lean';adapted=pc.C/'Case322Adapt.lean'
    if original.exists()or adapted.exists():raise ValueError('preserve existing control')
    original.write_text(ORIGINAL);adapted.write_text(adapt(ORIGINAL,IMPORTS))
    mapping=[dict(original_path=str(original),original_sha256=sha(original.read_bytes()),adapted_path=str(adapted),
                  adapted_sha256=sha(adapted.read_bytes()),import_map=IMPORTS)]
    # This exact mapping/expected source is frozen before compiler/auditor contact.
    (H/'source-control-mapping-v1.json').write_text(json.dumps(mapping,indent=2)+'\n')
    checks=[];check('exact explicit import adaptation clean',validate(mapping,mapping),checks)
    pc.run([pc.LEAN,'-o',pc.C/'Case322Adapt.olean',adapted],'adaptation-compile',0)
    record=pc.audit(['Case322Adapt'],'adaptation-audit')
    check('actual adapted import binding',record['inventories'][0]['imports'].count('Case322CleanA')==1,checks)
    check('actual adapted stored theorem',len(pc.rows(record,'Case322Adapt.token'))==1,checks)
    for tag,mut in [('missing',lambda r:r.pop()),('duplicate',lambda r:r.append(copy.deepcopy(r[0]))),
                    ('sourceSHA',lambda r:r[0].update(original_sha256='0'*64)),('adaptedSHA',lambda r:r[0].update(adapted_sha256='0'*64)),
                    ('path',lambda r:r[0].update(adapted_path=str(original))),('importmap',lambda r:r[0].update(import_map={'Case322Dep':'Case322CleanB'}))]:
        bad=copy.deepcopy(mapping);mut(bad)
        check('mapping corruption '+tag,pc.v.catches(lambda:validate(bad,mapping)),checks)
        check('mapping clean twin '+tag,validate(mapping,mapping),checks)
    for tag,text in [('comment',ORIGINAL+'\n-- modified source\n'),('type',ORIGINAL.replace('token : True','token : True ∧ True')),
                     ('body',ORIGINAL.replace('Case322Same.token','True.intro')),('import',ORIGINAL.replace('Case322Dep','Case322CleanB'))]:
        corrupt=D/(tag+'.lean');corrupt.write_text(text)
        bad=copy.deepcopy(mapping);bad[0]['original_path']=str(corrupt)
        check('actual changed source '+tag,pc.v.catches(lambda:validate(bad,bad)),checks)
    out=dict(checks=checks,passed=len(checks),mapping=mapping,seconds=time.perf_counter()-start,
             scope='exact source/import adaptation controls on fresh own bytes; installed Std/Init trusted, no scientific candidate')
    (H/'source-controls-output-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(passed=len(checks),seconds=out['seconds'])))
if __name__=='__main__':
    try:main()
    except Exception:
        with(H/'source-control-failures-v1.log').open('a')as f:f.write(traceback.format_exc()+'\n')
        raise
