"""Resolve one lazy equation adoption without copying or loading author oleans."""
from pathlib import Path
import json,re,sys,hashlib
sys.dont_write_bytecode=True
import rebuild as R

def main():
 H=R.helper();build=R.HERE/'isolated-groups';base=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-rebuild-v1.json';r=json.loads(base.read_text())
 d=json.loads((R.HERE/'GROUP-ORIGIN-DIFFERENCE-v1.json').read_text());assert not d['only_author'] and not d['only_fresh'];assert d['adoptions']==[{'name':'RMAF.agreement.eq_1','author_origin':'GroupStateFacts','fresh_origin':'GroupForward'}]
 original=R.ROOT/'results/algorithm-universal233-forest-groups-20261015T103546623214Z/ModuleInventory.lean'
 authorimports=re.findall(r'^import ([^\n]+)',original.read_text(),re.M);print('AUTHORIMPORTS',authorimports)
 contexts={'AllImports':r['modules'],'AuthorImports':[x for y in authorimports for x in y.split()]}
 builds=[];values={};origins={}
 for name,mods in contexts.items():
  module='FreshEq'+name
  text=''.join('import '+m+'\n' for m in mods)+'''import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let some c := env.find? `RMAF.agreement.eq_1 | throwError "missing equation"
 logInfo m!"TYPE|{repr c.type}"
 match c with
 | .thmInfo t => logInfo m!"VALUE|{repr t.value}"
 | _ => throwError "expected theorem"
 let some idx := env.getModuleIdxFor? `RMAF.agreement.eq_1 | throwError "missing origin"
 logInfo m!"ORIGIN|{env.header.moduleNames[idx.toNat]!}"
'''
  (build/(module+'.lean')).write_text(text);b=H.run(build,module);builds.append(b);assert b['exit']==0
  log=(build/(module+'.log')).read_text();values[name]=log[:log.index('ORIGIN|')];origins[name]=log.split('ORIGIN|')[1].strip()
 assert values['AllImports']==values['AuthorImports'], 'lazy theorem type/proof changed'
 assert origins=={'AllImports':'GroupForward','AuthorImports':'GroupStateFacts'},origins
 parsed=H.parse_audit(build/'FreshAudit.log',r['modules']);assert parsed['total']==849 and not parsed['forbidden']
 out={**r,'status':'PASS_SOURCE_ONLY_FULL_ORIGINS_WITH_CHECKED_LAZY_ADOPTION','audit':parsed,'origin_names_exact_author_match':True,'checked_lazy_adoption':{**d['adoptions'][0],'source_only_import_contexts':contexts,'exact_raw_type_and_proof_sha256':hashlib.sha256(values['AllImports'].encode()).hexdigest(),'builds':builds},'olean_hashes':{m:R.sha(build/(m+'.olean')) for m in r['modules']}}
 dest=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-rebuild-v2.json';dest.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],parsed['total'],out['checked_lazy_adoption']['exact_raw_type_and_proof_sha256'])
if __name__=='__main__':main()
