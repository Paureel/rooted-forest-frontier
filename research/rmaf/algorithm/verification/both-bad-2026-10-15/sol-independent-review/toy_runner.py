#!/usr/bin/env python3
"""One-shot full-origin Lean toy batch; no scientific imports or copied oleans."""
import copy
import hashlib
import json
import os
import pathlib
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
TOYS = HERE / "toys"
ROOT = pathlib.Path("/Users/paurel/Documents/ChatGPT/bootscience")
WRAPPER = ROOT / "bootloops-lean"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def run(module, expect=0):
    start = time.perf_counter()
    env = dict(os.environ, LEAN_PATH=str(TOYS))
    result = subprocess.run([str(WRAPPER), "-o", module + ".olean", module + ".lean"],
                            cwd=TOYS, env=env, capture_output=True, text=True, timeout=30)
    elapsed = time.perf_counter() - start
    (TOYS / (module + ".build.log")).write_text(result.stdout + result.stderr)
    record = {"module": module, "exit": result.returncode, "seconds": elapsed,
              "source_sha256": sha(TOYS / (module + ".lean")), "expected_exit": expect}
    if expect == 0:
        assert result.returncode == 0, record
    else:
        assert result.returncode != 0, record
    return record


def canonical(data):
    rows = data["records"]
    names = [r["name"] for r in rows]
    if len(names) != len(set(names)):
        raise ValueError("duplicate-origin")
    return {r["name"]: r for r in rows}


def adapter_errors(actual, claimed):
    errors = []
    if actual["sources"] != claimed["sources"]: errors.append("sources")
    if actual["imports"] != claimed["imports"]: errors.append("imports")
    if actual["all_modules"] != claimed["all_modules"]: errors.append("all_modules")
    try:
        a, b = canonical(actual), canonical(claimed)
        if set(a) != set(b): errors.append("origin-bijection")
        for name in set(a) & set(b):
            if a[name] != b[name]: errors.append("exact-record:" + name)
    except ValueError:
        errors.append("duplicate-origin")
    return errors


def main():
    summary = {"status": "RUNNING", "builds": [], "plants": [], "audit_sources": {}}
    summary["source_pins"] = {p.name: sha(p) for p in TOYS.glob("*.lean")}
    # Cold rebuild from source. Only this arm's own toy products are removed.
    for p in TOYS.glob("*.olean*"):
        p.unlink()
    for name in ["ToyGood", "ToyGenerated", "ToyUnused", "ToyPrivate", "OriginAudit"]:
        summary["builds"].append(run(name))
        write(HERE / "toy-results-v1.json", summary)
    summary["builds"].append(run("ToyFalse", expect=1))
    suites = {"Good": ["ToyGenerated"], "Unused": ["ToyGenerated", "ToyUnused"],
              "Private": ["ToyGenerated", "ToyPrivate"],
              "All": ["ToyGenerated", "ToyUnused", "ToyPrivate"]}
    audits = {}
    for suffix, modules in suites.items():
        name = "Audit" + suffix
        out = TOYS / (name + ".json")
        source = "import OriginAudit\n" + "".join("import " + m + "\n" for m in modules)
        source += 'audit_origins! "' + str(out) + '"\n'
        p = TOYS / (name + ".lean")
        p.write_text(source)
        # Adapter source frozen/hash recorded before its compile.
        summary["audit_sources"][name] = sha(p)
        write(HERE / "toy-results-v1.json", summary)
        summary["builds"].append(run(name))
        data = json.loads(out.read_text())
        data["sources"] = {p.name: sha(p) for p in TOYS.glob("Toy*.lean")}
        audits[suffix] = data
        assert bool(data["rejected"]) == (suffix != "Good"), suffix
        canonical(data)
        write(HERE / "toy-results-v1.json", summary)
    clean = audits["Good"]
    names = canonical(clean)
    for name in ["ToyGood.answer", "ToyGood.answer_ok", "ToyGood.privateProducer",
                 "ToyGenerated.Cell.rec", "ToyGenerated.read", "ToyGenerated.read_cell"]:
        assert name in names, name
    private = next(n for n in names if n.startswith("_private.ToyGood") and n.endswith("privateSeed"))
    generated = "ToyGenerated.Cell.rec"
    assert any(r["kind"] == "recursor" and r["origin"] == "ToyGenerated" for r in names.values())
    assert not adapter_errors(clean, copy.deepcopy(clean))
    mutations = []
    def plant(name, change, expected):
        v = copy.deepcopy(clean)
        change(v)
        errors = adapter_errors(clean, v)
        assert any(e.startswith(expected) for e in errors), (name, errors)
        mutations.append({"name": name, "caught": errors})
    first = clean["records"][0]["name"]
    plant("missing-origin", lambda v: v["records"].pop(), "origin-bijection")
    plant("duplicate-origin", lambda v: v["records"].append(v["records"][0]), "duplicate-origin")
    plant("wrong-origin", lambda v: v["records"][0].update(origin="ToyWrong"), "exact-record:")
    plant("missing-private", lambda v: v.update(records=[r for r in v["records"] if r["name"] != private]), "origin-bijection")
    plant("missing-generated", lambda v: v.update(records=[r for r in v["records"] if r["name"] != generated]), "origin-bijection")
    plant("wrong-source", lambda v: v["sources"].update({"ToyGood.lean": "0"*64}), "sources")
    plant("wrong-import", lambda v: v["imports"].append("HiddenScientific"), "imports")
    plant("wrong-type", lambda v: v["records"][0].update(type="FALSE-TYPE"), "exact-record:")
    plant("wrong-body", lambda v: v["records"][0].update(body="FALSE-BODY"), "exact-record:")
    plant("hidden-origin-axiom", lambda v: v["records"].append({"name": "Hidden.axiom", "origin": "ToyHidden", "kind": "axiom"}), "origin-bijection")
    summary["plants"] = mutations
    summary["clean_origin_count"] = len(names)
    summary["private_origin_seen"] = private
    summary["generated_origin_seen"] = generated
    summary["rejections"] = {k: v["rejected"] for k, v in audits.items()}
    summary["audit_output_sha256"] = {k: sha(TOYS / ("Audit" + k + ".json")) for k in suites}
    summary["status"] = "PASS"
    write(HERE / "toy-results-v1.json", summary)
    print(json.dumps({"status": "PASS", "builds": len(summary["builds"]),
                      "clean_origins": len(names), "plants_caught": len(mutations),
                      "private_origin": private, "generated_origin": generated}))


if __name__ == "__main__":
    main()
