# Origin control correction v3 (still PRE-CANDIDATE)

The v1 cross-module toy attempted to compare raw Expr records after private-name-only string normalization. The observed adapter failure is retained in toy-battery-v1.json. Changing the module name changes compiler hygienic binder names as well as private names and repr layout. Such renaming is not an import-only modification.

For the v2 toy battery, original, import-adapted and body-mutated copies are compiled as canonical module Clean in three isolated own-directory build roots. Original source imports Std; the adapter changes only that import to EmptyDependency, itself importing only Std. Type/body/extra/dependency/axiom records must agree exactly for the import adapter. The body plant changes publicPayload : Nat from 7 to 8 and must fail exact equality with an unchanged public type. No normalization or axiom allowlist change is authorized by this correction.
