"""Finish canonical positive replay; preserve failed exploratory CheckAPI probe."""
from pathlib import Path
import json,sys
sys.dont_write_bytecode=True
import rebuild as R

def main():
 old=json.loads(R.DEST.read_text());assert old['builds'][-1]['module']=='CheckAPI' and old['builds'][-1]['exit']==1
 assert all(x['exit']==0 for x in old['builds'][:-1]);H=R.helper()
 modules=[x['module'] for x in old['builds'][:-1]]
 assert len(modules)==43
 (R.BUILD/'FreshAllAudit.lean').write_text(H.audit_text(modules,'\nimport '.join(modules)))
 auditbuild=H.run(R.BUILD,'FreshAllAudit');assert auditbuild['exit']==0
 audit=H.parse_audit(R.BUILD/'FreshAllAudit.log',modules[:-1])
 zero=[x for x in audit['rows'] if x['module']=='Interfaces'];assert not zero
 audit['counts']['Interfaces']=0
 assert not audit['forbidden']
 result={**old,'status':'PASS_CANONICAL_41_AND_TWO_EXTRA_POSITIVE_MODULES','positive_modules':modules,'positive_module_count':43,'exploratory_excluded':{'module':'CheckAPI','declaration_free':True,'role':'Unimported exploratory API #check file, absent from canonical 41-module certificate. Four unknown API identifiers; retained as failed artifact, not altered or accepted.'},'audit_build':auditbuild,'audit':audit,'source_unchanged':all(R.sha(R.ROOT/x['copy'])==x['sha256'] and R.sha(R.ROOT/x['original'])==x['sha256'] for x in old['sources']),'olean_hashes':{m:R.sha(R.BUILD/(m+'.olean')) for m in modules}}
 assert result['source_unchanged']
 p=R.ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-rebuild-v2.json';p.write_text(json.dumps(result,indent=2)+'\n');print('POSITIVE',len(modules),'AUDIT',audit['total'],audit['axiom_union'])
if __name__=='__main__':main()
