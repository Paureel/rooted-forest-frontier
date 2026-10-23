"""Beginner-facing, source-linked map of the installed BootLoops toolkit."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

GROUPS = [
    ("reduction", "Reduction", "Make a large problem smaller.", "#5c75d6", ["kira-stack", "blade", "seedling", "winnow", "cutbasis", "numkin", "ffcapital", "formglue"]),
    ("geometry", "Geometry", "Find the structure and difficult points.", "#a486ce", ["landau-alphabet", "dipstick", "geotriage", "maxcut", "cosmoflow", "subtropica", "surd", "coalescer"]),
    ("transport", "Transport", "Carry an answer to new inputs.", "#6ba5c0", ["counterweight", "wayfinder", "famhar", "ratfit", "vopclose", "pmflow", "membound", "holonomic"]),
    ("evaluation", "Evaluation", "Turn a formula or integral into numbers.", "#3b958e", ["nestor", "longhand", "gpl-eval", "eichler", "ellipticus", "frobenius-boundary", "abacus", "amflow-kit"]),
    ("recognition", "Recognition", "Find an exact pattern behind the numbers.", "#d09d54", ["lockpick", "annihilator", "ansatzer", "galois", "rankscreen"]),
    ("arithmetic", "Arithmetic", "Keep track of numerical uncertainty.", "#cb7b89", ["baller", "eras", "clinch"]),
    ("evidence", "Evidence", "Compare scientific models with exact probabilities.", "#78a371", ["mixalot", "popcorn", "posq", "tropical-sampler"]),
    ("search", "Search", "Explore mathematical possibilities systematically.", "#9a98bc", ["terrier"]),
    ("integrity", "Integrity", "Check the inputs, outputs, and claims.", "#758b9a", ["dogtag", "trust", "gatekeeper", "emitall", "qinvert"]),
]

# Paraphrases of the installed tools/README.md rows; the source row is carried
# separately, with a line locator. These are a navigation taxonomy, not a claim
# that every tool is a dependency of every neighboring tool.
EXPLAIN = {
    "kira-stack": ("Kira Stack", "Reduce a large set of integral equations to a smaller set of master integrals.", "Many integrals", "Small basis"),
    "blade": ("Blade", "Arrange integral reduction into smaller blocks, without a Mathematica kernel.", "Integral family", "Reduced blocks"),
    "seedling": ("Seedling", "Check a new integral family and plan a reduction before spending compute.", "Family + targets", "Plan + checks"),
    "winnow": ("Winnow", "Eliminate equations using exact finite-field arithmetic, with witness receipts.", "Equations", "Reduction + witness"),
    "cutbasis": ("Cutbasis", "Use an integral’s geometry to choose a useful master-integral basis.", "Maximal cut", "Preferred basis"),
    "numkin": ("Numkin", "Freeze one input scale to help rescue a stalled reduction.", "Many scales", "Simpler samples"),
    "ffcapital": ("FFCapital", "Recover usable reconstruction state from an interrupted FireFly run.", "Saved state", "Recovered results"),
    "formglue": ("Formglue", "Connect FORM to symbolic tasks such as traces, color algebra, and rewriting.", "Symbolic terms", "Simplified terms"),
    "landau-alphabet": ("Landau Alphabet", "Find where an integral can become singular and which function letters it needs.", "Graph", "Singularities + letters"),
    "dipstick": ("Dipstick", "Probe the likely mathematical difficulty before a large calculation.", "Problem", "Triage"),
    "geotriage": ("GeoTriage", "Classify the geometry of an integral and assess whether value fitting is appropriate.", "Cut geometry", "Method choice"),
    "maxcut": ("Maxcut", "Study the maximal cut to classify geometry and construct useful equations.", "Integral family", "Cut + equations"),
    "cosmoflow": ("Cosmoflow", "Construct cosmological integrands and their alphabets from a site graph.", "Site graph", "Integrand + letters"),
    "subtropica": ("SubTropica", "Run a hyperlogarithm integration pipeline without a Wolfram kernel.", "Parametric integral", "Hyperlogarithms"),
    "surd": ("Surd", "Integrate a supported class of sliced integrals while keeping radical letters exact.", "Sliced integral", "Exact hyperlogs"),
    "coalescer": ("Coalescer", "Connect differential-equation solutions to their fractional-power branches.", "Operator + seed", "Branch coefficients"),
    "counterweight": ("Counterweight", "Rewrite suitable differential equations into a simpler canonical form.", "Connection", "Canonical form"),
    "wayfinder": ("Wayfinder", "Transport a known value along a differential equation, with certified checks.", "Boundary value", "Values elsewhere"),
    "famhar": ("Famhar", "Evaluate a configured integral family across multiple sheets.", "Family config", "Family values"),
    "ratfit": ("Ratfit", "Reconstruct exact rational functions from samples and test the reconstruction.", "Samples", "Rational function"),
    "vopclose": ("Vopclose", "Close a supported graded differential-equation system layer by layer.", "Graded equations", "Closed solution"),
    "pmflow": ("PMflow", "Evaluate supported cut-eikonal integral families using auxiliary-mass flow.", "PM integrals", "Numerical values"),
    "membound": ("Membound", "Compute soft-region boundary constants from supported frequency-space kernels.", "Kernel spec", "Boundary vector"),
    "holonomic": ("Holonomic", "Continue a solution of a holonomic differential equation with error enclosures.", "ODE + start", "Enclosed values"),
    "nestor": ("Nestor", "Evaluate an integral using high-precision quadrature with explicit error checks.", "Integrand", "Numerical reference"),
    "longhand": ("Longhand", "Compute integral values through an independent numerical route.", "Integral spec", "Independent values"),
    "gpl-eval": ("GPLEval", "Evaluate generalized polylogarithms at arbitrary precision.", "GPL formula", "Precise value"),
    "eichler": ("Eichler", "Evaluate periods and arithmetic-geometric quantities with certified tools.", "Period data", "Certified observables"),
    "ellipticus": ("Ellipticus", "Evaluate supported elliptic iterated integrals with certified values.", "Curve + word", "Enclosed value"),
    "frobenius-boundary": ("Frobenius", "Construct non-analytic boundary information from Frobenius branches.", "Reduction data", "Boundary branches"),
    "abacus": ("Abacus", "Count points on an abelian fourfold from its period lattice.", "Period lattice", "Exact point count"),
    "amflow-kit": ("AMFlow Kit", "Check AMFlow output and manage launch memory and cache bookkeeping.", "AMFlow output", "Output checks"),
    "lockpick": ("Lockpick", "Search a declared library of constants for an integer relation.", "Precise digits", "Candidate constant"),
    "annihilator": ("Annihilator", "Find a recurrence or differential operator in exact arithmetic, with certificates.", "Series", "Operator + proof"),
    "ansatzer": ("Ansatzer", "Construct and constrain the candidate function space for a bootstrap.", "Letters + rules", "Candidate space"),
    "galois": ("Galois", "Apply coaction constraints and reduce a supported ring of multiple-zeta relations.", "Formula bank", "Coaction constraints"),
    "rankscreen": ("Rankscreen", "Screen equation rank and inconsistency using multiple exact modular calculations.", "Exact equations", "Rank + consistency"),
    "baller": ("Baller", "Carry a value and a rigorous error radius through numerical calculations.", "Numbers + bounds", "Enclosed answer"),
    "eras": ("ERAS", "Keep error enclosures useful when many terms share the same uncertain parameter.", "Shared parameter", "Tighter enclosure"),
    "clinch": ("Clinch", "Certify local convergence of a fitted optimum with interval Newton methods.", "Fitted optimum", "Local certificate"),
    "mixalot": ("Mixalot", "Compute Bayesian evidence for supported mixture models with exact or certified methods.", "Counts + model", "Model evidence"),
    "popcorn": ("Popcorn", "Compute population-genetics likelihoods and frequency spectra with exact and certified tools.", "Genetic model", "Spectra + likelihood"),
    "posq": ("POSQ", "Compute certified two-sided Bayesian evidence and Bayes-factor quadrature.", "Model integrals", "Enclosed evidence"),
    "tropical-sampler": ("Tropical Sampler", "Use tropical geometry for importance sampling and supported certified quadrature.", "Integral", "Estimate or certificate"),
    "terrier": ("Terrier", "Explore string-theory vacua using period, lattice, and census tools.", "Lattice + periods", "Census + certificates"),
    "dogtag": ("Dogtag", "Check that a specified integral family has the intended identity and topology.", "Family spec", "Identity check"),
    "trust": ("Trust", "Verify reduction output with three checks from separate code lineages.", "Reduction output", "Independent checks"),
    "gatekeeper": ("Gatekeeper", "Track reference-data integrity and prevent fit data from certifying its own result.", "Values + provenance", "Honesty gate"),
    "emitall": ("Emitall", "Reproduce quoted numbers from their receipts and detect drift.", "Claims + receipts", "Claim checks"),
    "qinvert": ("Qinvert", "Check exact consistency of published summaries against partially released data.", "Summary statistics", "Consistency certificate"),
}

PROTOCOLS = [
    ("planted-truth", "Known truth", "Recover a known answer and catch a corrupted input before using real data."),
    ("independence-bookkeeping", "Independence", "Keep the checking route separate from the route that produced the answer."),
    ("acceptance-gate", "Acceptance", "Require independent, unused-point checks and stable precision before calling a result done."),
    ("constant-recognition", "Recognition", "Declare the constant library and coefficient bounds before searching for an exact form."),
    ("timing-discipline", "Timing", "Measure actual output progress before projecting a larger run."),
    ("tool-stewardship", "Stewardship", "Consult existing instruments before building another, and document what changes."),
    ("reading-contract", "Sources", "Assert only what the opened source supports, with a precise locator."),
    ("lit-review", "Literature", "Read the relevant papers and audit the search before claiming novelty."),
    ("prove-protocol", "Proof", "Use adversarial checking and distinct proving routes for mathematical statements."),
    ("referee-sim", "Review", "Test whether a scientific document answers the strongest objections from its audiences."),
    ("ref-check", "References", "Verify bibliography details against authoritative records."),
    ("prose-lint", "Writing", "Check scientific writing for clarity, unsupported claims, and untraceable numbers."),
]


def catalog():
    index = ROOT / "bootloops/tools/README.md"
    rows = {}
    for n, line in enumerate(index.read_text().splitlines(), 1):
        match = re.match(r"\| `([^`]+)/` \| (.*?) \| (selftest|partial|smoke|data-gated)", line)
        if match:
            rows[match[1]] = {"quote": match[2], "line": n, "class": match[3]}
    validation = json.loads((ROOT / "installation-validation.json").read_text())
    groups, tools = [], []
    for key, title, meaning, color, names in GROUPS:
        groups.append({"id": key, "name": title, "meaning": meaning, "color": color, "tools": names})
        for name in names:
            title, meaning, inp, out = EXPLAIN[name]
            folder = ROOT / "bootloops/tools" / name
            guide = next((p for p in (folder / "GUIDE.md", folder / "README.md") if p.is_file()), index)
            result = validation["packages"][name]
            tools.append({"id": name, "name": title, "group": key, "color": color, "meaning": meaning,
                          "input": inp, "output": out, "verification": result["status"],
                          "class": rows[name]["class"], "source": {"path": str(index.relative_to(ROOT)), "line": rows[name]["line"], "quote": rows[name]["quote"]},
                          "guide": str(guide.relative_to(ROOT)), "type": "tool"})
    assert len(tools) == len(rows) == 50 and {t["id"] for t in tools} == set(rows)
    protocols = []
    for name, title, meaning in PROTOCOLS:
        protocols.append({"id": name, "name": title, "meaning": meaning, "color": "#6e7bb7", "type": "protocol",
                          "guide": f".agents/skills/{name}/SKILL.md", "verification": "Installed", "input": "Scientific work", "output": "Checkable claims"})
    return {"groups": groups, "tools": tools, "protocols": protocols,
            "workspace": ROOT.name, "validation": validation["counts"],
            "operations": {"name": "Turnstile", "status": "Linux only", "meaning": "Queue jobs and budget shared RAM and CPU. Not available on this Mac.", "source": "bootloops/ops/turnstile/README.md"}}
