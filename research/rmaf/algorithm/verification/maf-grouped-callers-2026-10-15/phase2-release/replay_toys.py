"""Fresh execution of the exact preregistered Std-only origin corruption toys."""
import importlib.util,json,sys
sys.dont_write_bytecode=True
import rebuild as R
p=R.HERE.parent/'toy_gates.py';s=p.read_text().replace('HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]','HERE=Path(__file__).resolve().parent.parent;ROOT=HERE.parents[4]').replace("build=HERE/'toy-build-v1'","build=HERE/'phase2-release'/'toy-replay'").replace('algorithm-maf-grouped-prerelease-toy-gates-v1.json','algorithm-maf-grouped-fresh-review-toy-gates-v1.json')
q=R.HERE/'ReplayToys.py';q.write_text(s);spec=importlib.util.spec_from_file_location('fresh_standard_origin_toys',q);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.main()
(R.HERE/'toy-replay-adapter.json').write_text(json.dumps({'original_sha256':R.sha(p),'adapted_sha256':R.sha(q),'changes':'physical control root, fresh build folder and result filename only','no_scientific_candidate_imports':True},indent=2)+'\n')
