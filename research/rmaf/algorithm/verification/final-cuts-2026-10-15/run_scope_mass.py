"""One-shot literal consuming controls and actual raw-list mass readouts.
Expectations stay the frozen original bank;postcandidate proof instances explicit.
"""
from pathlib import Path
from fractions import Fraction
import os,subprocess,json,time,hashlib
b=Path(__file__).resolve().parent;root=b.parents[4];iso=b/'isolated';env=os.environ.copy();env['LEAN_PATH']=str(iso);h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((b/'MASS-CONTROL-PIN.json').read_text());cs={x['id']:x for x in json.loads((b/'CONTROL-PIN.json').read_text())['controls']}
def tree(x):return f'(.leaf {x})' if isinstance(x,int) else f'(.node {tree(x[0])} {tree(x[1])})'
def block(p):return '['+','.join('['+','.join(map(str,z))+']' for z in p)+']'
s='import Lean\nimport FinalWork\nopen Lean RMAF Universal233.CoreProgram Universal233.FinalCutRecovery Universal233.SourceCoverage\ndef main : IO Unit := do\n'
for c in pin['controls']:
 d=cs[c['receipt_id']]['input'];parts=c['base'].split('/');base=f'(mkRat {parts[0]} {parts[1]})' if len(parts)==2 else parts[0]
 s+=f' IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson {json.dumps(c["id"])}),("mass",toJson (toString (rawQMass {base} (generate {tree(d["tree"])} (blockColor {block(d["partition"])}) {c["cost"]}).outputs)))]).compress)\n'
(iso/'ReviewMass.lean').write_text(s)
post={'phase':'POST-CANDIDATE literal consumer instances; mathematical expectations already frozen before candidate','source_sha256':{n:h(iso/(n+'.lean')) for n in ['ReviewUse','ReviewFalseScope','ReviewMass']},'expected':['source/target AF literal original premise supplies transport','once-only c233/100 q3 work bound under actual checks','source-only crossed target remains false','two explicit false scope propositions rejected','12 rawQMass values equal immutable12 mass expectations']}
(b/'POST-CANDIDATE-SCOPE-PIN.json').write_text(json.dumps(post,indent=2)+'\n');rows=[]
for n,run,expected in [('ReviewUse',False,0),('ReviewFalseScope',False,1),('ReviewMass',True,0)]:
 args=[str(root/'bootloops-lean')]+(['--run'] if run else ['-o',n+'.olean'])+[n+'.lean'];t=time.monotonic();r=subprocess.run(args,cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);p=b/'candidate-logs'/(n+'.log');p.write_text(r.stdout);assert r.returncode==expected,(n,r.stdout)
 count=r.stdout.count('Tactic `decide` proved that the proposition')
 if expected:assert count==2,r.stdout
 rows.append({'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':h(iso/(n+'.lean')),'log_sha256':h(p),'explicit_false_diagnostics':count})
 if n=='ReviewMass':actual={x['id']:x['mass'] for line in r.stdout.splitlines() if line.startswith('RAW_MASS ') for x in [json.loads(line.split(' ',1)[1])]}
assert len(actual)==12
for c in pin['controls']:
 assert Fraction(actual[c['id']])==Fraction(c['expected'])
 assert Fraction(c['base'])**(-c['false_cost'])!=Fraction(actual[c['id']])
 assert 2*Fraction(actual[c['id']])!=Fraction(c['expected'])
out={'status':'PASS-SCOPED-CONSUMERS-AND-ACTUAL-MASS','runs':rows,'actual_masses':actual,'mass_clean':12,'wrong_cost_claims_rejected':12,'duplicate_mass_claims_rejected':12,'separate_postcandidate_explicit_false_controls':2,'additional_replications':0,'all_three_main_milestones':'OPEN'}
(b/'POST-CANDIDATE-SCOPE-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
