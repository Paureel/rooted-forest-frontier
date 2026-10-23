# Readout namespace failure

Readouts_v1 failed before execution because `Integration.vertices` is not defined. Preserve generated source, generator and compiler log. Use the actual defining namespace from the exact released CoreGraph source for v2, with unchanged trees, expected values and candidate definitions. No test value was altered and no mathematical mismatch was observed.

Readouts_v2 also failed because CoreGraph was an incorrect inferred namespace. A restricted source definition search located the actual function at Executable.lean:8 in Universal233.HardParent. v3 uses that fully qualified name; v1/v2 and both compiler failures remain intact. This is a test-adapter error, not a candidate error.
