"""Clean compilation and all-theorem axiom audit; no proof implementation imports."""
from pathlib import Path
import re,json,hashlib,subprocess,time
base=Path(__file__).resolve().parent;root=base.parents[4]
files=[('geometry','Geometry.lean','RuntimeRepairGeometry'),('recurrence','RepairArithmetic.lean','RuntimeRepairRecurrence'),('adversary','AdversaryArithmetic.lean','RepairAdversary')]
rows=[]
for folder,name,ns in files:
    src=base.parent/folder/name;text=src.read_text();ths=re.findall(r'^theorem\s+(\w+)',text,re.M)
    # Comment stripping precedes declaration audit.
    clean=re.sub(r'/\-.*?\-/','',text,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
    assert not re.search(r'\b(sorry|axiom|native_decide|admit)\b',clean)
    audit=base/(name[:-5]+'Audit.lean');audit.write_text(text+'\n'+'\n'.join('#print axioms '+ns+'.'+t for t in ths)+'\n')
    start=time.perf_counter();run=subprocess.run([str(root/'bootloops-lean'),str(audit)],cwd=root,capture_output=True,text=True,timeout=30)
    log=base/(name[:-5]+'Audit.log');log.write_text(run.stdout+run.stderr)
    row={'source':str(src.relative_to(root)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'audit_copy':str(audit.relative_to(root)),'theorems':ths,'exit_code':run.returncode,'seconds':time.perf_counter()-start,'output':run.stdout+run.stderr}
    rows.append(row)
    assert run.returncode==0,row
    for ax in re.findall(r'depends on axioms: \[([^]]*)\]',run.stdout):
        assert set(x.strip() for x in ax.split(',') if x.strip())<= {'propext','Classical.choice','Quot.sound'},ax
(base/'lean-compile-receipt.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ('source','exit_code','seconds')} for r in rows]))
