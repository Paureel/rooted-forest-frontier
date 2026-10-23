# Budget-local selected common binding

This author extension binds the actual selected `.one` common call to the
actual ordinary callback at the current remaining cut budget q. All main
milestones and independent acceptance remain OPEN.

`runSelectedCommon actual T S a b d q` is exactly
`(runCommon T S a b d q actual).join`. Its executable body has no IH parameter,
callback replacement or mathematical completion. `actual_source_ih` uses only
`forall r<q, LocalOrdinaryIH r actual`: every actual source job is proper and
has budget strictly below q, so the corresponding r-specific IH supplies its
literal bounded contract. A local callback result of None is justified from
completeness; a returned forest uses soundness and global minimum from that
same local IH. No all-budget OrdinaryIH is assumed.

For an actual admitted `.one` selector output, `selected_bounded` applies the
completed source primitive. `selected_sound_minimum` proves every returned
forest agrees, fits q and has no more components than any original agreement
forest. `selected_complete` proves any feasible forest at q yields an actual
return, with no more components. `selected_none_iff` identifies None exactly
with absence of an original agreement forest within q. Positive agreement
forests have positive length, so the component-count minimum is derived
without an implicit root label or parameter shift.

This is a small transitive extension of two frozen DEVELOPMENT releases.
The315 dependency modules retain exact source/olean pins from the completed
selector release. Only ForestMinimumCompletion, OrdinaryBinding and
BindingControls are newly source-rebuilt here; the first supplies the exact
frozen LocalOrdinaryIH definition. Its proof-only ghost definitions remain
recorded as nonproof bodies and are absent from runSelectedCommon's executable
dependencies. No ghost is substituted for actual and no runtime bound is
claimed. The initial cut convention remains q=k_opt-1.

The producer extractor and its fresh modified-generator control receipt are
reused unchanged, with exact immutable hashes. Compact audit records retain
all nonproof/opaque bodies and actual theorem proof AX references; only
proof expression text is omitted. Full sources and proof oleans are pinned.
Wrong join/budget/refund controls reject mathematically; failed draft source
and import/control attempts remain retained. Fresh nonauthor semantic,
interface and prose review is pending.
