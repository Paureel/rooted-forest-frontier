# Toy pilot timing and retained setup failure

ToyGood real0.34s. OriginAudit timing in toy-audit-pilot-v1.log. This is first same-machine/configuration compiler pilot; five fixed module builds and four audit entries are bounded below60s, with conservative10s projection after confirming auditor success. Progress is compiled named toy modules and emitted full-origin JSON files.

Retained setup failure: initial SHA command ran from toys/ while using root-relative paths and zsh reported no matches. The next newline command still compiled ToyGood. Frozen toy source text and preregistration existed before compile, but the requested precompile SHA receipt was absent. It was generated immediately afterward before any other compile, with no source edit. This is an ordering deviation, not erased; ToyGood pilot is provisional on that narrow receipt-order condition. A clean cold rebuild from the now-hashed same bytes is required before READY.
