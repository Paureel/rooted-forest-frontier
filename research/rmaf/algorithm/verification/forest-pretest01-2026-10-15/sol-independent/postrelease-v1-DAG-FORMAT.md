# Lossless stored-expression record format

Each gzip member stream contains newline-delimited `PRODUCER ` JSON records.
`raw-module` records retain module index/name, producer array index,
declared-name denominator, extra names and the actual stored producer.
`coalesced` records separately retain the selected value and reported module
index origin. Neither replaces the raw records. Partial failed streams are
retained but excluded from the completed-coverage denominator.

Every stored producer records its ConstantInfo kind, structural Name,
universe parameters, type DAG, ordinary body DAG when present, recursor rule
constructor/field-count/RHS DAGs and definition safety/hints/mutual names.
Inductives and constructors have types rather than ordinary value bodies.
All 3,004 expected definition/theorem bodies are present in this closure.

Expression DAG nodes follow Lean 4.35.0 Expr constructors: bvar, fvar, mvar,
sort, const, app, lam, forall, let, nat/string literal, mdata and proj. Nodes
have zero-based IDs and child IDs always precede the parent. The record's
root ID identifies the full expression. Binder names/annotations and let
nondependency bits remain explicit. Names are recursively anonymous,
string-component or numeric-component tags. Levels are zero/succ/max/imax/
param/mvar tagged trees. ExprStructEq preserves binder names/annotations
while sharing genuinely equal subexpressions; alpha-equivalence is not the
deduplication rule.

Metadata entries retain ordered Name/DataValue pairs. Original v1 streams
support string/bool/name/Nat/Int values and refuse Syntax, so every completed
v1 stream has no omitted Syntax metadata. Postcontact v2 supports the full
Syntax constructors (missing/node/atom/ident), SourceInfo constructors,
raw substring backing strings and byte positions, canonical-source bits and
preresolved namespace/declaration names and field lists. Backing source
strings are interned in a per-expression source_strings array; each raw
substring stores its string index, start byte and stop byte. An absent
source_strings field in v1 means an empty array. No normalization erases
metadata or proof terms.

The convenience refs field contains direct Expr.const names. The dependency
analysis independently traverses the lossless DAG and also counts Expr.proj
structure names plus recursor-rule constructor names. Universe parameters,
bound/free variable identifiers and names occurring only inside metadata
are not declaration references. All occurrence reference sets are retained
before name grouping; equal-type theorem variants preserve the union of
both private splitter dependencies. Every nonproof body remains distinct.

The format encodes stored scientific declarations. It does not serialize
the full installed Init/Std environment, compiler IR, code-generation
attributes or machine execution. Those trust and runtime questions remain
explicit qualifications in the report.
