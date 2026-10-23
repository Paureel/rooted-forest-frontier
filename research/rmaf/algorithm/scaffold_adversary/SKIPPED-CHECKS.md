# Toolkit skipped checks and unavailable engines

These entries are copied from the retained official runner output tails. Package PASS does not imply every optional or data-dependent leg ran. The complete per-package records available from the runner are retained in bootloops-check-all-results.json.

## ansatzer

```
  [SKIP] no alphabet.json supplied (set COLLAPSE_T5_ALPHABET)
  [OK ] disabled honesty: SKIPPED: got True  want ==True
```

## cosmoflow

```
SKIP  deep-oracle-probe (heavy leg, not run by default; use --deep)
```

## dipstick

```
order_member: SKIP (Oscar not in the active Julia project (set DIPSTICK_JULIA_PROJECT))
order_shim: SKIP (Oscar not in the active Julia project (set DIPSTICK_JULIA_PROJECT))
count: SKIP (msolve not on PATH (see toolkit/external/TOOLS.md; MSOLVE_BIN overrides))
cycletype: SKIP (msolve not on PATH (see toolkit/external/TOOLS.md; MSOLVE_BIN overrides))
```

## landau-alphabet

```
[groebner] SKIP (neither msolve nor Singular installed -- install either to enable; escalation backend not exercised)
```

## longhand

```
[U/F front end] SKIP (pySecDec not installed -- propagator front end not exercised; pip install pySecDec to enable)
SKIPPED [1] tests/test_disteval.py:156: no compiled package on this host (LONGHAND_DISTEVAL_PACKAGE_DIR, or the older name PYSECDEC_POINT_PACKAGE_DIR, unset): the package is not a fixture
SKIPPED [1] tests/test_disteval.py:373: pySecDec 1.6.6 with pySecDecContrib is not importable on this host: the stand-in check imports it
SKIPPED [1] tests/test_disteval.py:678: pySecDec 1.6.6 with pySecDecContrib is not importable on this host: the stand-in check imports it
29 passed, 3 skipped in 9.92s
```

## qinvert

```
50 passed, 2 skipped, 14 subtests passed in 0.44s
```

## amflow-kit

```
SKIPPED [1] tests/test_cgroup_procs_size.py:58: no cgroup v2 '0::' line in /proc/self/cgroup
SKIPPED [1] tests/test_cgroup_procs_size.py:109: no cgroup v2 '0::' line in /proc/self/cgroup: no live leaf
SKIPPED [1] tests/test_compare_amflow_json.py:380: COMPARE_AMFLOW_JSON_PREVIOUS unset: the previous tool's file is not named
SKIPPED [1] tests/test_compare_amflow_json.py:687: COMPARE_AMFLOW_JSON_PREVIOUS unset: the previous tool's file is not named
7 failed, 42 passed, 4 skipped in 49.19s
```

## blade

```
s are SKIPPED (the bank is not distributed with this repository); running the self-contained raw-system section only
  [SKIP] I.rawsys end-to-end: binaries ['redg1', 'fitrel', 'fflowcli'] not built under BLADE_BIN_DIR=/Users/paurel/Documents/ChatGPT/bootscience/blade/bin -- build the blade fork to arm this leg
```

## clinch

```
clinch selftest PASS — self-contained legs green; receipt-gated legs (L3/L6 and L4's receipt sub-leg) skipped: CLINCH_REFERENCE_DIR unset (the reference results are not shipped; see GUIDE.md)
```

## cutbasis

```
SKIP reducer  no Kira executable found (PATH has no 'kira'; pass --kira PATH or set KIRA=/path/to/kira)
OVERALL PASS: 8/9 checks pass; skipped: reducer (no Kira executable found (PATH has no 'kira'; pass --kira PATH or set KIRA=/path/to/kira))
```

## eichler

```
T  SKIP  theta9: no battery ships (reference receipts not distributed; 10 fixture files present, engine = Eichler.jl via EICHLER_PROJECT)
eichler selftest: ALL PASS (M + G; L6 refused by name; T skipped by name) wall 2.3s  outdir=/var/folders/jh/tgnbthq142z_by1ws1k2n0kc0000gn/T/tmp.PAAT6i4FhY
```

## formglue

```
============================= formglue named skips =============================
SKIPPED tools/formglue/tests/test_form_oracle.py::test_knowns_two_precisions: no FORM binary found (form): install a float-capable FORM 5 or point FORM5_BIN at one (see GUIDE.md)
SKIPPED tools/formglue/tests/test_form_oracle.py::test_tornheim_independent_cross_check: no FORM binary found (form): install a float-capable FORM 5 or point FORM5_BIN at one (see GUIDE.md)
SKIPPED tools/formglue/tests/test_form_oracle.py::test_mutation_control: no FORM binary found (form): install a float-capable FORM 5 or point FORM5_BIN at one (see GUIDE.md)
15 passed, 3 skipped in 0.47s
```

## frobenius-boundary

```
producer_lint: SKIPPED (FROB_PRODUCER_LINT unset)
producer_lint: SKIPPED (FROB_PRODUCER_LINT unset)
```

## gpl-eval

```
/Users/paurel/Documents/ChatGPT/bootscience/bootloops/tools/gpl-eval/GPLEval.jl/src/ginac_gpl.cpp:16:10: fatal error: 'ginac/ginac.h' file not found
┌ Warning: GiNaC oracle unavailable — skipping the GiNaC cross-check legs. To enable them install the GiNaC C++ library (e.g. `apt install libginac-dev pkg-config` plus g++), then delete src/ginac_gpl if a stale binary exists and rerun.
```

## holonomic

```
smoke: SKIP (SageMath not on PATH ('sage'; install from https://www.sagemath.org or conda-forge, then `sage -pip install ore_algebra`; HOLONOMIC_SAGE overrides the executable))
```

## kira-stack

```
S3 SKIP  Kira-derived GPL tools (pyred_weight, ffsave_degree_census) not found in /Users/paurel/Documents/ChatGPT/bootscience/kira/bootloops-tools — check out ../kira or set BOOTLOOPS_KIRA_TOOLS
M2 SKIP  Kira-derived GPL tools (pyred_weight, ffsave_degree_census) not found in /Users/paurel/Documents/ChatGPT/bootscience/kira/bootloops-tools — check out ../kira or set BOOTLOOPS_KIRA_TOOLS
S4 SKIP  Kira-derived GPL tools (pyred_weight, ffsave_degree_census) not found in /Users/paurel/Documents/ChatGPT/bootscience/kira/bootloops-tools — check out ../kira or set BOOTLOOPS_KIRA_TOOLS
M3 SKIP  Kira-derived GPL tools (pyred_weight, ffsave_degree_census) not found in /Users/paurel/Documents/ChatGPT/bootscience/kira/bootloops-tools — check out ../kira or set BOOTLOOPS_KIRA_TOOLS
kira-stack selftest: ALL PASS (3/3 run; S3 M2 S4 M3 SKIPPED by name, named ImportError verified)
```

## lockpick

```
[mplll_lattice] nemo batch failed (Nemo.lll failed: ERROR: LoadError: ArgumentError: Package Nemo not found in current path.
```

## maxcut

```
SKIP pent5: external data dir not present (set MAXCUT_R3C to a dir containing baikov_ls.py)
```

## pmflow

```
[SKIP] engine emit literal pin: engine source not present (/Users/paurel/Documents/ChatGPT/bootscience/amflow-cpp/src/pipeline/amfsystem.cpp not found; set AMFLOW_CPP_SRC to a checkout of the sibling repository amflow-cpp)
[SKIP] engine syntax gate: engine source tree absent (/Users/paurel/Documents/ChatGPT/bootscience/amflow-cpp; set AMFLOW_CPP_SRC to a checkout of the sibling repository amflow-cpp)
```

## posq

```
[SKIP] S2 kernel containment: POSQ-KERNEL-UNAVAILABLE: no runnable posq_kernel binary beside the source (not built yet, or FLINT shared-library / CPU architecture mismatch); build cache dir unwritable: [Errno 1] Operation not permitted: '/Users/paurel/.cache/posq' -- build it yourself (needs FLINT development headers): cc -O2 -o posq_kernel posq_kernel.c -lflint -lmpfr -lgmp -lm, then set POSQ_KERNEL to the result
```

## ratfit

```
53 passed, 2 skipped in 1.01s
```

## subtropica

```
E SKIP  driver suite: SUBTROPICA_HF_BIN is not set (or not a file) — the Julia suite needs a built HyperFLINT engine (deps/BUILD.md) plus SUBTROPICA_MZV_DATA and the instantiated Julia project; see GUIDE.md. Skipping is the designed engine-absent behavior, not breakage.
```

## surd

```
": [{"t": "9/13", "sigma": "1243", "charts_1_2_4_identical": true, "value_float": 0.0011407988632033401}, {"t": "19/9", "sigma": "1342", "charts_1_2_4_identical": true, "value_float": 1.0439207419537808e-05}, {"t": "5/2", "sigma": "1432", "charts_1_2_4_identical": true, "value_float": 2.0679097487432867e-05}], "wall_s": 2.2}, {"test": "n_N4_SLICE_data", "PASS": true, "sha16": "cc3bd6b61fec4a1d", "sha_expected": "cc3bd6b61fec4a1d", "n_letters_in_file": 34, "n_canonical_irreducible": 34, "wall_s": 0.1}, {"test": "a", "SKIP": "needs --data DIR or SURD_DATA (assembled files out/*.json.gz; not part of the package)"}, {"test": "b", "SKIP": "needs --data DIR or SURD_DATA (assembled files out/*.json.gz; not part of the package)"}, {"test": "c", "SKIP": "needs --data DIR or SURD_DATA (assembled files out/*.json.gz; not part of the package)"}, {"test": "d2", "SKIP": "needs --data DIR or SURD_DATA (assembled files out/*.json.gz; not part of the package)"}, {"test": "e", "SKIP": "needs --data DIR or SURD_DATA (assembled files out/*.json.gz; not part of the package)"}], "ALL_PASS": true, "n_ran": 4, "skipped": ["a", "b", "c", "d2", "e"], "wall_s": 3}
RESULT: PASS (4 ran, 5 skipped: a,b,c,d2,e)
```

## terrier

```
B.census    foldhnf [census/selftest_foldhnf.py]              SKIP (named)
B.census    distcert [census/selftest_distcert.py]            SKIP (named)
B.census    controlsampler [census/selftest_controlsampler.py SKIP (named)
B.periods   summation [periods/selftest_summation_reduced_u1s SKIP (named)
B.lattice   lpkill [lattice/selftest_lpkill_a1n_mustfail.py]  SKIP (named)
B.lattice   genusenum [lattice/selftest_genus_control_replay. SKIP (named)
18/34 passed, 16 named skip(s) in 46.2s wall
```

## trust

```
== test_banked (30 archived pairs + 84/84 retrofit + wrong-table MUST-FAIL; skips without RECEIPT_BANKED_ROOT) ==
SKIP: RECEIPT_BANKED_ROOT unset — the archived-reference leg needs the reference artifact store (not shipped)
```

## wayfinder

```
132 passed, 3 skipped in 76.67s (0:01:16)
```

## winnow

```
SKIP leg B: the archived wrong-table exhibit needs WINNOW_BANKED_ROOT
```

