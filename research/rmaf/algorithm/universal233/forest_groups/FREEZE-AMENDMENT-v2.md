# Author freeze metadata amendment v2

The v1 freeze command redirected stdout to forest_groups/freeze.log. Its
manifest enumerated that output file while it was empty, before the command
finished writing its summary. A read-only hash audit found exactly one
mismatch: freeze.log. No proof source, frozen dependency, or replay result
changed. The canonical source-bound replay remains
results/algorithm-universal233-forest-groups-20261015T103546623214Z/certificate.json.

FOREST-GROUPS-MANIFEST-v2.json supersedes the v1 no-write inventory and records
the final freeze.log bytes. The original v1 manifest and seal remain preserved,
as does the original log. The v2 command emits its summary only to the tool
response, avoiding a live redirected file in its inventory. All v1 entries
other than the explained log were required to match before v2 was written.
The v2 inventory also preserves this amendment, its generator, and the original
v1 manifest and seal. No mathematical statement or acceptance status changes.

Use v2 for review and integrity checking. Every v2 immutable_files entry, v2
manifest, and v2 seal is now within the no-write boundary. build/ remains
excluded mutable development output. New replay receipt directories remain
permitted, and replay.py does not rewrite LATEST-REPLAY after the v1 freeze.
Independent nonauthor acceptance and all three main milestones remain OPEN.
