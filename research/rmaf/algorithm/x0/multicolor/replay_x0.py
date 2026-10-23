"""Replay unchanged core/comparator functions to fresh named local files."""
import argparse
import datetime
import gzip
import json
from pathlib import Path
import time
import run_x0 as instrument

parser=argparse.ArgumentParser()
parser.add_argument('--stage',choices=['controls','pilot','extension'],required=True)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--pilot',type=Path)
args=parser.parse_args()
if args.output.exists():
    raise SystemExit('refuse to overwrite existing replay output')
if args.stage=='extension' and args.pilot is None:
    raise SystemExit('extension requires a measured pilot receipt')
record={'stage':args.stage,'replay':True,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'file_sha256':instrument.hashes(),'scope':'Same finite scope and unchanged prototype/reference; no new certification.'}
started=time.perf_counter()
if args.stage=='controls':
    record.update(instrument.plant_controls());record['verdict']='PASS'
else:
    clean=instrument.plant_controls()
    assert clean['controls_passed']==clean['controls_total']==19
    if args.stage=='pilot':
        ns=[4]
    else:
        text=gzip.open(args.pilot,'rt').read() if args.pilot.suffix=='.gz' else args.pilot.read_text()
        prior=json.loads(text)
        assert prior['verdict']=='FINITE-NO-FIRE'
        assert len(prior['censuses'])==1 and prior['censuses'][0]['n']==4
        seconds=prior['elapsed_seconds'];projection=seconds/225*5460*16
        if projection>=7200:
            raise SystemExit('projection exceeds two hours; stop and restructure')
        decision={'pilot':str(args.pilot),'pilot_seconds':seconds,'projected_seconds':projection,
                  'size_slowdown_assumption':16,'n5_cases':5460,'recorded_before_execution':True}
        decision_path=args.output.with_name(args.output.name+'.timing.json')
        assert not decision_path.exists()
        decision_path.write_text(json.dumps(decision,indent=2)+'\n')
        record['timing_extension_decision']=decision
        ns=[1,2,3,5]
    record['censuses']=[instrument.census(n) for n in ns]
    record['verdict']='FIRE' if any(c['verdict']=='FIRE' for c in record['censuses']) else 'FINITE-NO-FIRE'
record['elapsed_seconds']=time.perf_counter()-started
record['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
if args.output.suffix=='.gz':
    with gzip.open(args.output,'wt') as f:
        json.dump(record,f,separators=(',',':'))
else:
    args.output.write_text(json.dumps(record,separators=(',',':'))+'\n')
print(json.dumps({'stage':args.stage,'verdict':record['verdict'],'output':str(args.output),
                  'compute_seconds':record['elapsed_seconds']}))
