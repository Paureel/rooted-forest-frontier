#!/usr/bin/env python3
"""Prepare disclosed own all-origin auditor and unchanged READY toy plants; no author auditor use."""
from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;R=P.parent/'sol-preparation-READY-v1/preparation';S=P/'src'
mods=['ToyClean','ToyUnused','ToyPrivate','ToyExternal','ToyUseExternal']
for n in ['OriginAudit']+mods:shutil.copyfile(R/'toy-src'/(n+'.lean'),S/(n+'.lean'))
for n,imports,wanted in [('AuditClean',['ToyClean'],['ToyClean']),('AuditPlanted',mods,['ToyClean','ToyUnused','ToyPrivate','ToyUseExternal']),('AuditScientific',json.loads((P/'source-integrity-v1.json').read_text())['positive_order'],json.loads((P/'source-integrity-v1.json').read_text())['positive_order'])]:
 (S/(n+'.lean')).write_text('import OriginAudit\n'+''.join('import '+m+'\n'for m in imports)+'\nrun_cmd ReleasedAudit.emit '+json.dumps(wanted)+'\n')
(P/'audit-source-freeze-v1.json').write_text(json.dumps({'before_execution':True,'support_lineage':'Unchanged own READY grouped audit; no author auditor/evaluator used','modules':[{'module':n,'source_sha256':hashlib.sha256((S/(n+'.lean')).read_bytes()).hexdigest()}for n in ['OriginAudit']+mods+['AuditClean','AuditPlanted','AuditScientific']],
'allowlist':['propext','Classical.choice','Quot.sound'],'required_origins':json.loads((P/'source-integrity-v1.json').read_text())['positive_order'],'scope':'Every released scientific originating declaration, private/generated/unused included; public-name prefix filtering forbidden'},indent=2)+'\n')
print('Own audit sources and planted controls frozen.')
