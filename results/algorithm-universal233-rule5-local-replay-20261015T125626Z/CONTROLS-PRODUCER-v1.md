# Post-contact producer-occurrence detector pin

Pinned 2026-10-15 before the new detector is applied to candidate modules.
This is an added instrument control, not an original blind mathematical plant.
It implements the root's ORIGIN-AUDIT-SCOPE-AMENDMENT-v1.md requirement; older
frozen histories and the original preproof receipt are preserved.

Std-only clean twins: producer A and producer B each store the same-named,
same-typed theorem `AuditShared : True`; B also stores a distinct clean theorem.
The hostile producer replaces its stored `AuditShared` theorem by a custom
axiom of the same name/type and retains its own clean theorem. Importing A and
the hostile producer must fail on that stored axiom, even if the merged
environment resolves AuditShared to A. Clean A+B must pass.

Each expected producer's actual stored ModuleData.constants array is traversed
by array index, with constNames matched to the actual ConstantInfo.name. The
record includes producer/index, resolved origin, declaration kind, raw type,
raw body, referenced constants and dependency axiom references. Every direct
custom axiom is rejected, including unused/private/coalesced occurrences.
Only Classical.choice, propext and Quot.sound may occur in dependency closures.

Fail criteria: any custom axiom, non-toolchain unpinned module path, source
byte/adapted-byte mismatch, missing producer, missing or duplicated occurrence,
missing/duplicated summary, undecidable producer attribution. The parser must
reject a removed row and an added duplicate row from the clean control. All
clean and hostile logs remain with the author receipt. No external independent
credit is attached to author-run detector or source replays.
