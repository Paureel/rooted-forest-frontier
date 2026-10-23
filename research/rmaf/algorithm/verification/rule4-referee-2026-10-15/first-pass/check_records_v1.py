#!/usr/bin/env python3
"""One-session document checker; no scientific build/execution or toolkit registration.

Checks hashes, exact quotations, receipt fields and source/type tokens; renders only
the local Markdown subset. Consulted emitall/GUIDE.md; it lacks combined source-byte,
line-span and render checks. This wrapper is for this bounded review only.
"""
from pathlib import Path
from hashlib import sha256
from html import escape
from html.parser import HTMLParser
import json
import re
import sys
import time

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
ALG = "research/rmaf/algorithm/"
PRE = ALG + "verification/rule4-2026-10-15/sol-independent/"
POST = PRE + "postrelease-v1/"
AUTHOR = ALG + "universal233/rule4/"
READS = {}

def read(path, human="machine-only"):
    p = ROOT / path
    b = p.read_bytes()
    READS.setdefault(str(p), {"path": str(p), "bytes": len(b), "sha256": sha256(b).hexdigest(),
                             "human_read": human, "machine_contacts": []})
    READS[str(p)]["machine_contacts"].append("read bytes")
    return b

def obj(path):
    return json.loads(read(path))

def pointer(value, keys):
    for key in keys:
        value = value[key]
    return value

def evaluate(item):
    b = read(item["path"])
    kind = item["kind"]
    if kind == "hash":
        actual = sha256(b).hexdigest()
    elif kind == "quote":
        lines = b.decode().splitlines()
        span = "\n".join(lines[item["start"]-1:item["end"]])
        actual = item["quote"] in span
    elif kind == "field":
        actual = pointer(json.loads(b), item["keys"])
    elif kind == "length":
        actual = len(pointer(json.loads(b), item["keys"]))
    elif kind == "tokens":
        lines = b.decode().splitlines()
        span = "\n".join(lines[item["start"]-1:item["end"]])
        actual = all(token in span for token in item["tokens"])
    elif kind == "table_width":
        actual = len(b.decode().splitlines()[item["line"]-1].strip().strip("|").split("|"))
    else:
        raise ValueError(kind)
    if type(actual) is not type(item["expected"]) or actual != item["expected"]:
        raise AssertionError({"id": item["id"], "expected": item["expected"], "actual": actual})
    return {**item, "actual": actual, "passed": True}

def inline(s):
    pieces = s.split("`")
    return "".join(("<code>"+escape(p)+"</code>") if i % 2 else escape(p)
                   for i,p in enumerate(pieces))

def render(md):
    lines = md.splitlines()
    parts, widths = [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if line.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].startswith("|"):
                cells = [v.strip() for v in lines[i].strip().strip("|").split("|")]
                rows.append(cells)
                i += 1
            width = len(rows[0])
            if any(len(r) != width for r in rows):
                raise ValueError("unequal table widths")
            widths.append({"columns": width, "data_rows": len(rows)-2})
            parts.append("<table>")
            for j, row in enumerate(rows):
                if j == 1 and all(re.fullmatch(r":?-+:?", c) for c in row):
                    continue
                tag = "th" if j == 0 else "td"
                parts.append("<tr>" + "".join(f"<{tag}>{inline(c)}</{tag}>" for c in row) + "</tr>")
            parts.append("</table>")
            continue
        heading = re.match(r"^(#{1,6}) (.*)$", line)
        if heading:
            level = len(heading[1])
            parts.append(f"<h{level}>{inline(heading[2])}</h{level}>")
            i += 1
            continue
        if line.startswith("- "):
            parts.append("<ul>")
            while i < len(lines) and lines[i].startswith("- "):
                parts.append("<li>" + inline(lines[i][2:]) + "</li>")
                i += 1
            parts.append("</ul>")
            continue
        para = []
        while i < len(lines) and lines[i].strip() and not lines[i].startswith(("|", "#", "- ")):
            para.append(lines[i])
            i += 1
        parts.append("<p>" + inline(" ".join(para)) + "</p>")
    html = '<!doctype html><html><head><meta charset="utf-8"><style>body{font-family:system-ui;max-width:1100px;margin:2rem auto;line-height:1.5}table{border-collapse:collapse;width:100%;font-size:.88rem}td,th{border:1px solid #aaa;padding:.4rem;vertical-align:top}code{white-space:normal}</style></head><body>' + "\n".join(parts) + "</body></html>"
    return html, widths

class TextReader(HTMLParser):
    def __init__(self):
        super().__init__()
        self.text, self.skip = [], False
    def handle_starttag(self, tag, attrs):
        if tag == "style": self.skip = True
    def handle_endtag(self, tag):
        if tag == "style": self.skip = False
        if tag in {"p", "h1", "h2", "h3", "tr", "li"}: self.text.append("\n")
        if tag in {"td", "th"}: self.text.append("\t")
    def handle_data(self, data):
        if not self.skip: self.text.append(data)

def text_of(html):
    parser = TextReader()
    parser.feed(html)
    parser.close()
    return "".join(parser.text)

def write_json(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")

def controls():
    fixture = OUT / "checker-control.txt"
    fixture.write_bytes(b"abc")
    fixture_json = OUT / "checker-control.json"
    fixture_json.write_text('{"count":2,"items":["a","b"],"empty":[]}\n')
    rel = str(fixture.relative_to(ROOT))
    relj = str(fixture_json.relative_to(ROOT))
    base = [
        {"id":"control-hash", "kind":"hash", "path":rel, "expected":"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"},
        {"id":"control-quote", "kind":"quote", "path":rel,"start":1,"end":1,"quote":"abc","expected":True},
        {"id":"control-field", "kind":"field", "path":relj,"keys":["count"],"expected":2},
        {"id":"control-length", "kind":"length", "path":relj,"keys":["items"],"expected":2},
        {"id":"control-tokens", "kind":"tokens", "path":rel,"start":1,"end":1,"tokens":["a","bc"],"expected":True},
        {"id":"control-null", "kind":"length", "path":relj,"keys":["empty"],"expected":0},
    ]
    result = [evaluate(x) for x in base]
    for item in base[:-1]:
        bad = dict(item)
        if item["kind"] == "hash": bad["expected"] = "0"*64
        elif item["kind"] == "quote": bad["quote"] = "abd"
        elif item["kind"] == "tokens": bad["tokens"] = ["missing"]
        else: bad["expected"] = 3
        try:
            evaluate(bad)
        except AssertionError:
            result.append({"id": item["id"]+"-corruption", "caught":True})
        else:
            raise AssertionError("uncaught planted corruption " + item["id"])
    plant = "# Control heading\n\nControl `token` paragraph.\n\n| A | B |\n|---|---|\n| one | two |\n| three | four |\n"
    h, widths = render(plant)
    (OUT/"renderer-control.md").write_text(plant)
    (OUT/"renderer-control.html").write_text(h)
    t = text_of((OUT/"renderer-control.html").read_text())
    (OUT/"renderer-control.rendered.txt").write_text(t)
    assert widths == [{"columns":2,"data_rows":2}]
    assert "Control heading" in t and "Control token paragraph." in t
    assert "one\ttwo\t" in t and "three\tfour\t" in t
    try:
        render("| A | B |\n|---|---|\n| missing |\n")
    except ValueError:
        result.append({"id":"malformed-table", "caught":True})
    else: raise AssertionError("malformed table accepted")
    result.append({"id":"renderer-positive", "passed":True,"table":widths})
    write_json("CONTROL-RESULTS-v1.json", result)
    return result

def main():
    began = time.monotonic()
    control_results = controls()  # Same entry point, before real record evaluation.
    specs = []
    def add(id, kind, path, expected, **kw):
        specs.append(dict(id=id, kind=kind, path=path, expected=expected, **kw))
    for id, path, expected in [
        ("target",str((OUT/"TARGET-v1.md").relative_to(ROOT)),"152f1f7c6dda3d9ecc72c08ac75cf3341353cf32d8f8e1f5d675d4e2d227ec34"),
        ("author-manifest",AUTHOR+"RULE4-MANIFEST-v1.json","6f38a6930b5f3794207a66c93a890d5e89d4a6562d820d291533ae58b2f50940"),
        ("review-manifest",POST+"SOURCE-REVIEW-MANIFEST-v1.json","cfb8cfe53f90de2e7b9c1dad0fdafbecd4c83257e76dd67d7e76fee15605d949"),
        ("seal",POST+"SOURCE-REVIEW-SEAL-v1.json","c58c349f769698d5f15f062b7f8856f34f05dfc51240eed593e2f37fa52f4d13")]:
        add(id,"hash",path,expected)
    add("author-immutable-count","length",AUTHOR+"RULE4-MANIFEST-v1.json",929,keys=["immutable_files"])
    add("author-external-count","length",AUTHOR+"RULE4-MANIFEST-v1.json",87,keys=["external_input_pins"])
    add("review-member-count","length",POST+"SOURCE-REVIEW-MANIFEST-v1.json",660,keys=["files"])
    quotes = [
        ("Q1",AUTHOR+"RESULT.md",3,3,"The actual original-graph Rule4 cover is proved in Lean."),
        ("Q2",ALG+"RULE4-REVIEW-STATUS-v1.md",3,3,"This is a local result for an attributed published-rule scaffold."),
        ("Q3",AUTHOR+"INTERFACE.md",18,18,"Exact residual original walks, region coverage/separation, original leaf sets, every suppressed vertex, no leafless regions and exact cut-list length."),
        ("Q4",AUTHOR+"RESULT.md",58,58,"Author construction is complete at this local consuming interface."),
        ("Q5",POST+"FINAL-REVIEW.md",10,10,"The supplied child must be exact, minimum and complete for each actual query."),
        ("Q6",POST+"FINAL-REVIEW.md",11,11,"No custom axiom or uncovered ConstantInfo was found."),
        ("Q7",POST+"FINAL-REVIEW.md",17,17,"Materialization alone is therefore not an invalid-cut runtime guard."),
        ("Q8",POST+"FINAL-REVIEW.md",19,19,"it uses lexical forest ties, while Lean keeps the earlier equal minimum."),
        ("Q9",ALG+"RULE4-REVIEW-STATUS-v1.md",3,3,"Algorithm, Correctness and Smaller base remain OPEN."),
        ("Q9b",POST+"FINAL-REVIEW.md",9,9,"Finite searches support the source reading; they are not the universal proof."),
        ("Q10",ALG+"RULE4-REVIEW-STATUS-v1.md",11,11,"These are different units, not proof-completion percentages."),
    ]
    report = (OUT/"referee_sim_rule4-v1.md").read_text()
    for id,path,start,end,quote in quotes:
        assert quote in report, id + " absent from report"
        add(id,"quote",path,True,start=start,end=end,quote=quote)
    for id,path,keys,expected in [
        ("python-checks",POST+"runtime-python-all-v2.json",["passed"],252),
        ("lean-checks",POST+"lean-runtime-all-v2-validation.json",["passed"],288),
        ("calls",POST+"lean-runtime-all-v2-validation.json",["actual_callback_traces"],90),
        ("guard-classes",POST+"guard-readout-validation-v3.json",["passed_guard_cases"],6),
        ("producers",POST+"producer-validation-all.json",["producers"],95),
        ("stored",POST+"producer-validation-all.json",["stored_occurrences"],3513),
        ("resolved",POST+"producer-validation-all.json",["unique_names"],3487),
        ("axioms",POST+"producer-validation-all.json",["axiom_union"],["Classical.choice","Quot.sound","propext"]),
        ("raw-record-bytes",POST+"SOURCE-REVIEW-SEAL-v1.json",["full_stored_type_body_record_bytes"],2135010213),
        ("gzip-record-bytes",POST+"SOURCE-REVIEW-SEAL-v1.json",["full_stored_type_body_gzip_bytes"],45755671),
        ("installed-modules",POST+"installed-used-pins.json",["imported_standard_modules"],1147),
        ("installed-files",POST+"installed-used-pins.json",["count"],4594),
        ("historical-members",POST+"SOURCE-REVIEW-SEAL-v1.json",["evidence","pre_READY_members_unchanged"],99),
        ("milestones",POST+"SOURCE-REVIEW-SEAL-v1.json",["main_milestones"],"ALL_OPEN"),
        ("novelty-open",POST+"SOURCE-REVIEW-SEAL-v1.json",["novelty"],"OPEN"),
        ("pixel-false",POST+"SOURCE-REVIEW-SEAL-v1.json",["evidence","pixel_visual_inspection"],False),
    ]: add(id,"field",path,expected,keys=keys)
    for id,path,keys,expected in [
        ("mutation-count",POST+"lean-runtime-all-v2-validation.json",["mutations"],7),
        ("false-errors-v2",POST+"false-source-execution-v2.json",["error_headers"],5),
        ("python-check-records",POST+"runtime-python-all-v2.json",["checks"],252),
        ("lean-check-records",POST+"lean-runtime-all-v2-validation.json",["checks"],288),
    ]: add(id,"length",path,expected,keys=keys)
    for id,path,start,end,tokens in [
        ("guards",POST+"cold-source/Rule4Selector.lean",40,67,["(leaves T).Nodup","(leaves S).Nodup","(leaves T).Perm (leaves S)","pendantOriginal S p.1 p.2","pendantOriginal T p.1 p.2","subtreeLabels S s.cHead = [s.c]","priority : Priority T S","admission : LocalGuard T S raw"]),
        ("exact-child",POST+"cold-source/Rule4Solve.lean",9,18,["ForestState.agrees (some b.target) b.sourceForest F","ForestState.additionalCost b.sourceForest F ≤ r","∀ H, ChildFeasible b r H → G.length ≤ H.length","∃ G, child b r = some G"]),
        ("affordable-once",POST+"cold-source/Rule4Solve.lean",20,30,["if b.cost ≤ q then (child b (q-b.cost)).toList else []","(solveForest s q child).bind (FinalCutRecovery.recover S)"]),
        ("raw-branch-and-roles",POST+"cold-source/Rule4Program.lean",68,82,["structure Branch where","target : Tree","source : Tree","cuts : List RMAF.Vertex","[⟨T,S,[s.raw.cHead,s.raw.xHead],false⟩","⟨S,T,pendantOriginal T s.raw.a s.raw.c,true⟩"]),
        ("nonroot-antichain",POST+"cold-source/Rule4LiteralCuts.lean",10,14,["distinct : cuts.Nodup","actual : ∀ q","nonroot : ∀ q","incomparable : ∀ q r"]),
        ("original-hulls",POST+"cold-source/RMAF.lean",109,157,["abbrev Vertex := List Bool","def minimalVertices","prependSide false ls ++ prependSide true rs","pairwiseEmbeddings t bs && pairwiseEmbeddings u bs"]),
        ("printed-local-cover",POST+"interface-types.stdout",1,1000,["Universal233.Rule4.actual_rule4_cover","LE.le.{0} (List.length.{0} G) (List.length.{0} F)","Universal233.Rule4.selected_cut_properties","Universal233.Rule4.ExactChild child b (HSub.hSub.{0, 0, 0} q b.cost)","Universal233.CutRealization.RealizedOutput S o","Universal233.FinalCutRecovery.meterRecover S P).value","sourceQ : Eq.{1} (RMAF.pairwiseEmbeddings S Q) true"]),
    ]: add(id,"tokens",path,True,start=start,end=end,tokens=tokens)
    add("historical-table-raw-width","table_width",AUTHOR+"INTERFACE.md",4,line=26)
    results = [evaluate(spec) for spec in specs]
    manifests = [(AUTHOR+"RULE4-MANIFEST-v1.json","immutable_files",ROOT),
                 (POST+"SOURCE-REVIEW-MANIFEST-v1.json","files",ROOT/POST)]
    membership = []
    for path,key,base in manifests:
        index = {str((base/x["path"]).resolve()):x for x in obj(path)[key]}
        for p,item in list(READS.items()):
            if p not in index: continue
            pin = index[p]
            assert item["sha256"] == pin["sha256"], p
            assert item["bytes"] == pin.get("bytes", item["bytes"]), p
            membership.append({"path":p,"manifest":path,"matched":True})
    human = {
        str((OUT/"TARGET-v1.md").relative_to(ROOT)):"complete; first contact",
        ALG+"RULE4-REVIEW-STATUS-v1.md":"complete 1–13",
        **{AUTHOR+n:"complete" for n in ["RESULT.md","INTERFACE.md","COST-MODEL.md","FIRST-GAP.md"]},
        **{POST+n:"complete" for n in ["FINAL-REVIEW.md","CONSUMER-TRACE.md","SOURCE-WORK.md","REVIEW.md","SOURCE-REVIEW-SEAL-v1.json","interface-types.stdout"]},
        POST+"cold-source/Rule4Selector.lean":"1–95 only",
        POST+"cold-source/Rule4Solve.lean":"1–37 and 57–102 only",
        POST+"cold-source/Rule4Program.lean":"68–84 only",
        POST+"cold-source/Rule4LiteralCuts.lean":"1–17 only",
        POST+"cold-source/RMAF.lean":"100–160 only",
        PRE+"CONTACTS-v1.json":"complete",
        PRE+"REVIEW-SKELETON-v1.md":"failure excerpts 29–35,97–117,129–145 only",
        "bootloops/tools/README.md":"complete across displayed slices; initial batch truncated then explicit slices",
        "bootloops/tools/emitall/GUIDE.md":"complete",
        **{".agents/skills/"+n+"/SKILL.md":"complete; prose-lint repeated slices repaired initial display cap" for n in ["referee-sim","prose-lint","reading-contract","tool-stewardship","planted-truth","independence-bookkeeping"]},
    }
    for path,scope in human.items():
        read(path,scope)
        READS[str(ROOT/path)]["human_read"] = scope
    for item in READS.values():
        item["machine_contacts"] = sorted(set(item["machine_contacts"]))
    write_json("READ-LEDGER-v1.json", list(READS.values()))
    write_json("FACT-CHECKS-v1.json", {"scope":"retrieved record consistency only; no scientific replay", "checks":results,"manifest_membership":membership,"seconds":time.monotonic()-began})
    initial = OUT/"INITIAL-CONTACT-PINS-v1.json"
    current = {p: x["sha256"] for p,x in READS.items() if not p.startswith(str(OUT)+"/")}
    if initial.exists():
        assert json.loads(initial.read_text()) == current, "external named contacts changed"
    else: write_json(initial.name,current)
    render_results = []
    for name in ["RULE4-SCOPE-COMPANION-v1.md","referee_sim_rule4-v1.md","PROPOSED-EDITS-v1.md"]:
        h,widths = render((OUT/name).read_text())
        (OUT/(name+".html")).write_text(h)
        t = text_of((OUT/(name+".html")).read_text())
        (OUT/(name+".rendered.txt")).write_text(t)
        lower = re.findall(r".{0,40}\. [a-z]{3,}.{0,60}",t)
        render_results.append({"file":name,"tables":widths,"text_bytes":len(t.encode()),"lowercase_after_period_candidates":lower,"pixel_inspection":False})
    write_json("RENDER-CHECKS-v1.json",render_results)
    print(json.dumps({"controls":len(control_results),"record_checks":len(results),"named_manifest_matches":len(membership),"rendered_documents":len(render_results),"seconds":time.monotonic()-began}))

if __name__ == "__main__":
    main()
