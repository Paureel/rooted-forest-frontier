"""Copy only the pinned scientific source closure into an empty own cold tree."""
import hashlib,json,pathlib,time
HERE=pathlib.Path(__file__).resolve().parent
def main():
 start=time.perf_counter();plan=json.loads((HERE/'COLD-SOURCE-PLAN-v1.json').read_text())
 if plan['command_alerts']:raise RuntimeError('unreviewed executable source commands')
 cold=HERE/'cold';cold.mkdir()
 for name in plan['order']:
  row=plan['modules'][name];raw=pathlib.Path(row['source']).read_bytes()
  assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
  dst=cold/(name.replace('.','/')+'.lean');dst.parent.mkdir(exist_ok=True,parents=True);dst.write_bytes(raw)
 print(json.dumps({'sources_copied':len(plan['order']),'scientific_binaries_copied':0,'seconds':time.perf_counter()-start}))
if __name__=='__main__':main()
