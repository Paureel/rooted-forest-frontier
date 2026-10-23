# Std-only audit toy preregistration v1

Before first Lean toy execution. Custom scientific math imports: none. ToyGood imports Std only; ToyGenerated imports ToyGood and tests standard generated inductive/recursor/function constants. ToyUnused and ToyPrivate import ToyGood. Auditor imports Lean compiler API only, does not become a scientific-origin module. No scientific oleans copied.

Frozen positive truth: answer=7 and privateProducer=11, read(cell19)=19, innocent True. FalseTwin 0=1 must fail compilation. Unused custom axiom False must compile but full-origin audit reject it despite innocent theorem. Private custom axiom False plus a private producer must be included and rejected. Generated Cell recursors/constructors and read equations must occur in the raw origin audit, not only advertised theorem names.

Every constant whose ACTUAL origin begins Toy* is emitted, with module index/name, kind, raw type/body expression, all direct dependencies and transitive axiom list. Exact imports are emitted. Custom-origin axioms are rejected globally even unused; inherited nonstandard axioms also reject. Standard allowed axioms are propext, Classical.choice, Quot.sound. This scanner establishes full-map comparison mechanics, not mathematical correctness of candidate code.

On a clean full actual-origin map: strict duplicate-free bijection required between claimed origin map and independently emitted actual map; source hashes, imports, each exact type/body and dependencies must match. Single mutation plants: delete origin; duplicate origin; wrong module; omit private; omit generated recursor; wrong source hash; wrong import; wrong type; wrong body; add hidden nonstandard axiom. Every plant must fail and unmodified clean twin pass. Adapter-body mutation cannot be blessed by retaining a source name. Freeze source hashes before compile. Preserve compilation failures and any harness corrections.

Timing: unknown; first compile ToyGood and auditor as pilot. Bound subsequent toy batch to5 modules and4 audit entries. If compilation exceeds60s stop/reassess. No broad scientific build before root RELEASE.
