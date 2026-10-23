"""Conservative author source-pool gate; separate from the AX gate.

Exact expression text is intentionally conservative. Unequal bodies of
theorems with the same proposition are allowed as proof variation. Other
duplicate declarations need equal types and equal definition/opaque bodies.
Other nonproof kinds are refused pending a complete metadata comparison.
"""
from collections import defaultdict

def inspect(rows):
    groups = defaultdict(list)
    for row in rows:
        groups[row['actual_name']].append(row)
    duplicates, rejected = [], []
    for name, group in sorted(groups.items()):
        if len(group) < 2:
            continue
        kinds = {r['kind'] for r in group}
        types = {r['type'] for r in group}
        bodies = {r['body'] for r in group}
        reason = None
        if len(kinds) != 1 or len(types) != 1:
            reason = 'KIND_OR_TYPE_MISMATCH'
        elif kinds == {'theorem'}:
            pass
        elif kinds <= {'definition', 'opaque'}:
            if len(bodies) != 1 or not all(r['has_body'] for r in group):
                reason = 'NONPROOF_VALUE_MISMATCH'
        else:
            reason = 'NONPROOF_METADATA_UNCHECKED'
        rec = {'name': name, 'occurrences': len(group),
               'producers': [r['producer'] for r in group],
               'kinds': sorted(kinds), 'bodies': len(bodies),
               'decision': reason or 'COMPATIBLE'}
        duplicates.append(rec)
        if reason:
            rejected.append(rec)
    return {'duplicates': duplicates, 'rejects': rejected}
