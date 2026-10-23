# Preregistered later source-bound Lean gate

Stage: PRE-CANDIDATE. No forthcoming candidate source is inspected or compiled.
Proceed only after root supplies the exact final author freeze and explicitly
releases the review. The final declared source list and hashes are inputs to
review, not premises proving coverage or cost.

1. Copy every released nonstandard .lean dependency into a new isolated build.
   Record its original absolute path, realpath, SHA256 and imported module
   names. Recursively account for every nonstandard import; resolve Std and
   compiler runtime to their actual installed origins and version. Reject
   missing source, undeclared/shadow module origins and hash drift. Set a
   clean LEAN_PATH; record the exact compiler command and environment policy.
   Never accept a stale .olean as evidence for a different source.
2. Audit all released source for sorry/admit/native_decide and custom axiom
   declarations, including dependency files. Enumerate all final exported
   theorem constants and retain #print axioms output. Allowed standard
   propext/Classical.choice/Quot.sound are recorded, not silently conflated
   with newly declared project axioms. Inspect implementation replacements,
   externs and unsafe computation when relevant to executable correspondence.
3. Recompile the released source in isolation and bind each stdout/stderr log,
   return code and .olean to the exact input hash. No compiler exit code alone
   certifies the graph interpretation, finite-budget coverage direction or
   raw-list weighted mass. Trace the actual final consuming theorem statement.
4. Execute explicit false-proposition controls with known false literal
   values: crossed generator has two cost2 outputs, not one output and not
   cost>=3; concatenating its receipt with itself retains four entries; the
   strict singleton partition refines [[0,1],[2]], while the reverse fails.
   These controls must fail because the proposition is false, rather than an
   unavailable import, syntax error, unrelated timeout or missing instance.
5. Execute a planted custom axiom/source-origin corruption on an isolated toy
   copy. The source/axiom or origin auditor must reject it even if Lean would
   otherwise compile it. Keep a clean matching source twin. Never place the
   planted declaration in candidate or trusted source.
6. Only after these gates, run independently frozen original-graph controls
   against released exports and reconstruct the original cut witness,
   finite-budget F-refines-Q coverage, raw LIST multiplicity and rational mass.
   Any universal assertion remains OPEN until actual source-model proof and
   consuming scope agree. This preparation adds no replication count and no
   algorithm/correctness/base acceptance.

The frozen preparation checker executes textual custom-axiom and origin/hash
clean/corrupted twins now. Candidate compilation and candidate proposition
controls are deferred until root release, as required.
