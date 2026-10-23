# Tree address semantics

`TreeAddresses.lean` defines actual vertices and selected leaf occurrences for the unchanged executable `RMAF.Tree`. It proves the interpretation of both lists, occurrence validity, label functionality, unique addresses under leaf-label nodup, the consequences for each `RMAF.Instance` side, terminal nonemptiness and address-list nodup.

Use this module when interpreting the extractor's ambient tree or terminal set. The definitions preserve every leaf occurrence, including repeated labels. The module contains no extractor or leastness theorem.

Run the retained author replay from the workspace root:

```sh
./bootloops-python research/rmaf/bridge_review/leastness/address_semantics/audit_semantics.py
```

A successful replay produces `replay-receipt.json`, fresh compiled dependencies in `replay-deps/`, and the logs in `replay-logs/`. The false semantic statements and malformed proof deliberately fail compilation; the replay requires those failures. The Python fixtures use exact comparisons and require each corrupt candidate to fail beside a passing clean twin. The frozen expected values are also checked in Lean.

The source imports only unchanged `RMAF`. Parent verification must rebuild that source, this module and the consuming statements independently. Author replay success alone does not complete the proof protocol's fresh nonauthor review requirement. `JOURNAL.md` records provenance, attempts and limitations.
