from pathlib import Path
import os,subprocess,json,hashlib,time
root=Path(__file__).resolve().parents[5];base=Path(__file__).resolve().parent;iso=base/'isolated'
env=os.environ.copy();env['LEAN_PATH']=str(iso)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def execute(n):
 t=time.monotonic();p=subprocess.run([str(root/'bootloops-lean'),n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 log=base/(n+'.log');log.write_text(p.stdout)
 assert p.returncode==0,(n,p.stdout)
 rows=[json.loads(line.split('WORK_REVIEW_ROW ',1)[1]) for line in p.stdout.splitlines() if 'WORK_REVIEW_ROW ' in line]
 assert len(rows)==len({r['name'] for r in rows})
 return rows,{'module':n,'seconds':time.monotonic()-t,'source_sha256':sha(iso/(n+'.lean')),'log_sha256':sha(log)}
rows,build=execute('ReviewInventory')
allowed={'propext','Classical.choice','Quot.sound'}
def gate(rs,names):
 if len(rs)!=len({r['name'] for r in rs}):return False
 if {r['name'] for r in rs}!=names:return False
 return all(r['kind']!='axiom' and set(r['axioms'])<=allowed for r in rs)
assert gate(rows,{r['name'] for r in rows})
# Corrupt exact inventory names, retaining individual records as clean twins.
names={r['name'] for r in rows};assert not gate(rows[1:],names);assert not gate(rows+[rows[0]],names)
source=(iso/'ReviewInventory.lean').read_text()
source=source.replace('import Controls','import ReviewPrivatePlant').replace('let wanted := ["RMAF"','let wanted := ["ReviewPrivatePlant","RMAF"')
(iso/'ReviewPlantInventory.lean').write_text(source)
plants,pbuild=execute('ReviewPlantInventory')
plants=[r for r in plants if r['origin']=='ReviewPrivatePlant']
assert len(plants)>=3
assert any(r['kind']=='axiom' and '_private.' in r['name'] for r in plants)
assert any('privateBill' in r['name'] and '_private.' in r['name'] for r in plants)
assert not gate(plants,{r['name'] for r in plants})
# Same inventory mechanism accepts a clean theorem module.
clean=source.replace('import ReviewPrivatePlant','import ReviewClean').replace('"ReviewPrivatePlant"','"ReviewClean"')
(iso/'ReviewCleanInventory.lean').write_text(clean)
cleans,cbuild=execute('ReviewCleanInventory');cleans=[r for r in cleans if r['origin']=='ReviewClean'];assert gate(cleans,{r['name'] for r in cleans});assert cleans
counts={}
for r in rows:counts[r['origin']]=counts.get(r['origin'],0)+1
result={'status':'PASS-COMPLETE-ORIGIN-INVENTORY','total':len(rows),'module_counts':counts,'private_name_count':sum('_private.' in r['name'] for r in rows),'kind_counts':{k:sum(r['kind']==k for r in rows) for k in sorted({r['kind'] for r in rows})},'axiom_union':sorted(set(a for r in rows for a in r['axioms'])),'all_rows':rows,'builds':[build,pbuild,cbuild],'controls':{'missing_record':'REJECTED','duplicate_record':'REJECTED','private_custom_axiom':'REJECTED','clean_twin':'ACCEPTED'},'private_plant_rows':plants,'clean_twin_rows':cleans}
(base/'ORIGIN-INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['all_rows','private_plant_rows','clean_twin_rows']}))
