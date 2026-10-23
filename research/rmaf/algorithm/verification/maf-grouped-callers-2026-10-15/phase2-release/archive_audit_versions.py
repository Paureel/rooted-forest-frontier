"""Keep both origin-audit generations source/log bound.

The v2 runner reused audit log basenames. Archive its exact bytes, then replay
the unchanged v1 runner's group imports to restore the original v1 log hashes.
Neither scientific sources nor the original v1 result receipt are rewritten.
"""
import json,sys
sys.dont_write_bytecode=True
import rebuild as R
def main():
    h=R.HERE;b=h/'isolated-groups';H=R.helper()
    dest=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-audit-v2.json'
    d=json.loads(dest.read_text());v2=next(x for x in d['packages'] if x['arm']=='groups')
    archives=[]
    for field in ('audit_build','dual_build','literal_print_build'):
        row=v2[field];name=row['module']
        for suffix in ('lean','log'):
            src=b/(name+'.'+suffix);out=b/(name+'-v2.'+('txt' if suffix=='lean' else suffix))
            out.write_bytes(src.read_bytes());archives.append({'source':str(src.relative_to(R.ROOT)),'archive':str(out.relative_to(R.ROOT)),'sha256':R.sha(out)})
            if suffix=='log':assert R.sha(out)==row['log_sha256'];row['log']=str(out.relative_to(R.ROOT))
    dest.write_text(json.dumps(d,indent=2)+'\n')
    base=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-rebuild-v2.json').read_text())
    mods=base['modules']+['FreshReadout','FreshConsumer','FreshFalseTwins']
    text=H.audit_text(mods,'\nimport '.join(mods));(b/'FreshFinalAudit.lean').write_text(text)
    dual=text.replace('for (n, info) in env.constants do','for (n, info) in (env.constants.map₁.toList ++ env.constants.map₂.toList) do');(b/'FreshDualAudit.lean').write_text(dual)
    printer=(b/'FreshPrintAxioms-v2.txt').read_text().replace('\nimport FreshChild','').replace(', `FreshChild','');(b/'FreshPrintAxioms.lean').write_text(printer)
    old=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-audit-v1.json').read_text());old=next(x for x in old['packages'] if x['arm']=='groups')
    replay=[]
    for field in ('audit_build','dual_build','literal_print_build'):
        r=H.run(b,old[field]['module']);assert r['exit']==0 and r['log_sha256']==old[field]['log_sha256'];replay.append(r)
    out={'status':'BOTH_AUDIT_GENERATIONS_PRESERVED','v2_exact_archives':archives,'v1_original_log_hashes_reproduced':True,'v1_replay':replay,'qualification':'V2 originally reused audit basenames. Its exact bytes are now versioned; unchanged V1 content was replayed to reproduce all three original log hashes. No proof/control expectation changed.'}
    (h/'audit-version-preservation.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
if __name__=='__main__':main()
