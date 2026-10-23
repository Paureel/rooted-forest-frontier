# Sol independent precontact controls

These controls prepare a later review of a complete ordinary rooted MAF solver. They contain no candidate code or candidate results. `FIXTURES-v1.json` contains answers derived by hand before execution. `WORKFILE.md` records the contact order, original failures, repairs and measured pilots. `READY-v1.json` lists the files and pins; its detached hash is supplied to root.

`semantic_controls.py` implements two methods. One deletes every subset of graph edges and compares the resulting leaf-bearing component shapes. The other enumerates set partitions, recursively prunes rooted restrictions and checks pairwise disjoint original vertex hulls. They share input tree bytes, a block-order convention, Python's exact integers and this author; they share no validity, restriction or hull callback. Both independently refuse malformed tree inputs. These methods are finite test instruments and are not part of a proposed accelerated solver.

The semantic output reports exact partition sets, component minima and explicit census denominators. `controls` must reproduce the seven hand truth cases, seven validity cases and six malformed inputs in both routes; it must reject the wrong optimum, incomplete cover and missing/duplicate rows. The incomplete cover retains optimum 2 while deleting a required witness. `pilot 3` and `pilot 4` compare all ordered pairs of the 3 and 15 sibling-unordered labeled rooted binary trees, respectively. No larger census has been run.

`lean/Producer.lean` is a fresh environment inspector. `lean/StoredInvoke.lean` imports its compiled producer and executes the stored `main`. The producer serializes complete nonproof and opaque values, complete declaration metadata and recursor RHSs, and walks actual full proof bodies before omitting their text. `integrity_controls.py` parses every retained expression constructor, checks actual body references/node counts, verifies source/binary/producer paths and hashes, traverses custom axiom dependencies and rejects incomplete rows or bodies. Its lock records byte/path identity rather than mathematical truth. Arbitrary expression metadata is retained as repr by the producer and explicitly refused by the auditor pending a calibrated exact encoder.

Run the existing frozen semantic and integrity batteries without modifying records:

```sh
BOOTLOOPS_MONITOR_DISABLE=1 ./bootloops-python research/rmaf/algorithm/verification/fast-ordinary-solver-2026-10-15/sol-independent/semantic_controls.py controls
BOOTLOOPS_MONITOR_DISABLE=1 ./bootloops-python research/rmaf/algorithm/verification/fast-ordinary-solver-2026-10-15/sol-independent/integrity_controls.py controls
```

For retained process evidence, launch each command through `bounded_run.py UNIQUE-LABEL -- COMMAND ...`. The supervisor retains compressed shards and a JSON process receipt, including launch failures and cap stops. New producer runs need distinct labels and a new lock revision; the frozen auditor deliberately refuses ambiguous duplicate historical labels. The final source and integrity batteries were run through this supervisor. All wrapper invocations set `BOOTLOOPS_MONITOR_DISABLE=1` to prevent shared dashboard writes.

The supervisor uses a 59s stop threshold, 64MiB raw capture, 16MiB line, 256MiB total new compressed-output cap and a live 3GiB free-space floor. Test environment variables can only lower the time/raw/line limits. A clean process passes; deliberately lowered caps retain named raw/line/time stops, and a nonexistent executable retains a launch error. These are resource checks, not scientific acceptance.

The installed compiler and standard Lean/Init/Std modules are declared trust. Candidate universality, functional correctness, termination, compiled-runtime correspondence, improved exponent and novelty remain open. The generic `bootloops-check` suite was not executed under this narrow own-controls/runtime contact license. The exact later review procedure is in `REPLAY-AND-INTERFACE-PLAN-v1.md`; it requires root's explicit immutable release before any candidate contact.
