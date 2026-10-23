# Compact audit scope

Actual stored producer occurrences are enumerated before coalescing. Every
actual ConstantInfo kind,type and non-theorem body (including nonproof opaque
data) is retained. The actual ConstantInfo.getUsedConstantsAsSet walks theorem
proof references; collectAxioms walks their dependency closure. Only theorem
proof expression TEXT is omitted from compact JSON. Full source and source-bound
olean bytes are pinned and retained. Imported-axiom proof and opaque dependency
plants demonstrate that omission does not bypass the AX rejection.

Fresh preflight v1 passed before candidate module compilation. Preflight v2
adds imported-axiom dependency plants before any candidate producer audit;
it is an added post-contact detector control, not an original blind fixture.
Both complete control directories and the earlier failed opaque control
compile are preserved. Literal fixture regression tests are post-contact.

Source audit runs one all-module master in an isolated source root and bounded
shards, with an8MiB uncompressed cap per producer and256MiB cumulative producer
output. Logs are compressed; disk floor3GiB is checked before each module.
Same-name stored types and full nonproof bodies must agree exactly; that
compatibility comparator first runs literal clean/corrupt plants. No fresh
nonauthor semantic/interface/prose acceptance is inferred.
