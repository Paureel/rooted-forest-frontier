# Frozen graph author checkpoint

Every immutable file in COMMON-SPLIT-GRAPH-MANIFEST-v1.json is frozen, including
the exact scientific source closure, detector pins, author instruments, failed
diagnostics, full producer-record archives and canonical replay evidence.
No further writes will occur to those files. Corrections require a new
versioned companion or package and new evidence, preserving this release.

Future Rule5.3.1 caller work belongs in a separate rule5_common_split_caller/
directory and new result directories. It is excluded from this graph release.
The mutable top-level algorithm workfile and progress card remain outside the
no-write boundary. Derived .olean/.ilean/.pyc files and __pycache__ are excluded
from the scientific byte manifest and may be recreated without changing any
frozen scientific source.
