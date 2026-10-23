# Large files and import coverage

The initial import includes eligible research history from the source workspace,
including failed approaches and original review records. Each imported file is
listed with its destination path, original path, byte count, modification time
and SHA-256 in docs/import/included-*.jsonl. The export interval, policy and
counts are recorded in [snapshot.json](import/snapshot.json).

## Exclusions

Each imported file is at most **1,048,576 bytes (1 MiB)**. Omission records in
docs/import/omitted-*.jsonl identify oversized files, compiled objects, local
databases, temporary files, symlinks and any possible credential pattern.
Runtime/cache directory records represent the entire excluded subtree.
Omitted-file hashes were not computed by the exporter; existing original
hash pins remain in the imported scientific manifests where available.
An omitted file is not a passing check or an intentionally withdrawn result.

The export does not upload virtual environments, native/Lean runtime installs,
Git metadata, caches, local dashboard databases, or the external BootLoops
checkouts. It preserves source .lean files even when a historical directory is
called build; compiled .olean/.ilean files are rebuilt locally.

## Restoring local evidence

Find a needed path in an omission shard, then obtain it from the original
local workspace at the same relative path. Compare against the original
scientific source manifest when it provides a hash. A recorded byte count
alone does not verify identity. Recreate runtime dependencies from their pins
rather than copying someone else's binary cache.

For rerunnable generated data, use the original generator and documented
settings in an isolated worktree. Compare mathematical payloads under the
original protocol; regenerated compression headers may differ. Do not pretend
an absent paper or raw log was read, a historical run was repeated, or a skipped
check passed. Some replay scripts retain source-workspace absolute paths or
need omitted inputs; inspect their prerequisites before running them.

New large local outputs belong outside Git, with a small versioned manifest
recording generation command, source hashes, size, content hash, scope and
storage location. No large-file hosting, LFS upload or external data bucket is
configured by this repository. Use make check to catch oversized tracked files.

## Snapshot limits

The original workspace was active and had no Git commits. This import is a
file-by-file copy over the recorded interval. Files that changed during their
copy were omitted explicitly. The manifest identifies each copied file's bytes;
it does not establish cross-file consistency or freeze a scientific release.
Original sources remain unchanged. The manifest covers the initial import,
not future research edits, which need their own versioned evidence records.
