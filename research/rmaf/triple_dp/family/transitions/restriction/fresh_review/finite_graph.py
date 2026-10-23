#!/usr/bin/env python3
"""One-shot independent finite restriction review; no project checker imports.

Constructed from TARGET.md, public controls, and shared Family definitions.
Graph BFS tests full paths; leaf labels never serve as region identities.
A PASS here is finite-control evidence, not a universal Lean proof.
"""
from collections import deque
from copy import deepcopy


class InvalidFamily(ValueError):
    pass


class OutsidePremise(ValueError):
    pass


def tree_graph(tree):
    """Return actual address vertices, adjacency, and leaf-label dictionary."""
    graph, leaves = {}, {}

    def visit(node, address, parent):
        graph[address] = set()
        if parent is not None:
            graph[address].add(parent)
            graph[parent].add(address)
        if isinstance(node, list):
            if len(node) != 2:
                raise InvalidFamily("tree node must have exactly two children")
            visit(node[0], address + "0", address)
            visit(node[1], address + "1", address)
        else:
            leaves[address] = node

    visit(tree, "", None)
    return graph, leaves


def graph_path(graph, start, goal):
    parents = {start: None}
    queue = deque([start])
    while queue:
        current = queue.popleft()
        if current == goal:
            path = []
            while current is not None:
                path.append(current)
                current = parents[current]
            return set(path)
        for neighbor in graph[current]:
            if neighbor not in parents:
                parents[neighbor] = current
                queue.append(neighbor)
    raise InvalidFamily("disconnected tree")


def validate_family(family):
    graph, leaf_labels = tree_graph(family["tree"])
    indices = family["indices"]
    regions = family["regions"]
    boundary = family["boundary"]
    if len(indices) != len(set(indices)):
        raise InvalidFamily("finite.nodup: duplicated index")
    if set(indices) != set(regions):
        raise InvalidFamily("finite.complete: enumeration differs from support domain")
    if boundary is not None and boundary not in indices:
        raise InvalidFamily("boundary is absent from index type")
    supports = {i: set(regions[i]) for i in indices}
    vertex_owners = {}
    witnesses = {}
    for index in indices:
        support = supports[index]
        if not support <= set(graph):
            raise InvalidFamily("bounded: support includes nonvertex")
        for a in support:
            for b in support:
                if not graph_path(graph, a, b) <= support:
                    raise InvalidFamily("convex: unique graph path leaves support")
        witness_addresses = sorted(support & set(leaf_labels))
        if not witness_addresses:
            raise InvalidFamily("labelled: index has no leaf vertex")
        witnesses[index] = [{"address": a, "label": leaf_labels[a]} for a in witness_addresses]
        for address in support:
            if address in vertex_owners:
                raise InvalidFamily("disjoint: vertex has two indices")
            vertex_owners[address] = index
    if not set(leaf_labels) <= set(vertex_owners):
        raise InvalidFamily("covers: uncovered leaf")
    root_owner = vertex_owners.get("")
    if root_owner != boundary:
        raise InvalidFamily("root_spec: root owner differs from boundary")
    return {
        "valid": True,
        "count": len(indices),
        "cost": len(indices) - int(boundary is not None),
        "charge": int(boundary is not None),
        "root_owner": root_owner,
        "leaf_witnesses": witnesses,
        "unused_vertices": sorted(set(graph) - set(vertex_owners)),
    }


def live_indices(parent, side):
    _, leaves = tree_graph(parent["tree"][side])
    prefix = str(side)
    return [i for i in parent["indices"]
            if any(prefix + leaf in set(parent["regions"][i]) for leaf in leaves)]


def open_branch_live(parent):
    boundary = parent["boundary"]
    if boundary is None:
        return True
    support = parent["regions"][boundary]
    return all(not any(a.startswith(str(side)) for a in support)
               or boundary in live_indices(parent, side) for side in (0, 1))


def restrict_child(parent, side):
    indices = live_indices(parent, side)
    regions = {i: sorted(a[1:] for a in set(parent["regions"][i])
                         if a.startswith(str(side))) for i in indices}
    owners = [i for i in indices if "" in regions[i]]
    if len(owners) > 1:
        raise InvalidFamily("restricted child has multiple root owners")
    return {"tree": parent["tree"][side], "indices": indices, "regions": regions,
            "boundary": owners[0] if owners else None}


def reassemble(left, right, kind):
    """Construct tagged transition output and its parent-index map from children.

    Closed/extended variants use disjoint sums. Merge uses one new boundary
    index and separately tagged residual indices; equal strings across child
    namespaces never identify unrelated residual regions.
    """
    families = (left, right)
    tags, regions, index_map = [], {}, {}
    boundary_tag = None
    if kind == "merge":
        if left["boundary"] is None or right["boundary"] is None:
            raise InvalidFamily("merge needs both child boundaries")
        merged_tag = ("joined",)
        tags.append(merged_tag)
        regions[merged_tag] = {""}
        index_map[merged_tag] = left["boundary"]
        if right["boundary"] != index_map[merged_tag]:
            raise InvalidFamily("merged boundaries have different original indices")
        for side, family in enumerate(families):
            regions[merged_tag].update(str(side) + a for a in family["regions"][family["boundary"]])
        boundary_tag = merged_tag
    for side, family in enumerate(families):
        for original in family["indices"]:
            if kind == "merge" and original == family["boundary"]:
                continue
            tag = ("L" if side == 0 else "R", original)
            tags.append(tag)
            regions[tag] = {str(side) + a for a in family["regions"][original]}
            index_map[tag] = original
            extended = kind == ("extendLeft" if side == 0 else "extendRight")
            if extended and original == family["boundary"]:
                regions[tag].add("")
                boundary_tag = tag
    if kind.startswith("extend") and boundary_tag is None:
        raise InvalidFamily("extension lacks distinguished child boundary")
    return {"tree": [left["tree"], right["tree"]], "indices": tags,
            "regions": regions, "boundary": boundary_tag}, index_map


def evaluate(parent):
    parent_report = validate_family(parent)
    if not isinstance(parent["tree"], list):
        raise InvalidFamily("restriction target requires node parent")
    live = [live_indices(parent, side) for side in (0, 1)]
    premise = open_branch_live(parent)
    children = [restrict_child(parent, side) for side in (0, 1)]
    if not premise:
        raise OutsidePremise("valid parent has occupied but leafless open branch")
    child_reports = [validate_family(child) for child in children]
    boundary = parent["boundary"]
    flags = [boundary is not None and boundary in indices for indices in live]
    if boundary is None:
        kind = "closeBoth"
    elif flags == [True, False]:
        kind = "extendLeft"
    elif flags == [False, True]:
        kind = "extendRight"
    elif flags == [True, True]:
        kind = "merge"
    else:
        raise AssertionError("leafless parent boundary would contradict labelled")
    occupied = [{i for i in parent["indices"] if any(a.startswith(str(side))
                  for a in parent["regions"][i])} for side in (0, 1)]
    assert all(set(live[s]) == occupied[s] for s in (0, 1)), "occupied/live mismatch"
    assert set(live[0]) | set(live[1]) == set(parent["indices"]), "index lost in children"
    overlap = set(live[0]) & set(live[1])
    assert overlap == ({boundary} if all(flags) else set()), "unexpected duplicated index"
    assert sum(c["count"] for c in child_reports) == parent_report["count"] + int(all(flags))
    charges = [report["charge"] for report in child_reports]
    toll = {"closeBoth": charges[0] + charges[1], "extendLeft": charges[1],
            "extendRight": charges[0], "merge": 0}[kind]
    assert parent_report["cost"] == sum(report["cost"] for report in child_reports) + toll
    assembled, index_map = reassemble(*children, kind)
    assembled_report = validate_family(assembled)
    map_values = list(index_map.values())
    assert len(map_values) == len(set(map_values)), "reassembly map is not injective"
    assert set(map_values) == set(parent["indices"]), "reassembly map is not surjective"
    exact_rows = []
    for tag in assembled["indices"]:
        original = index_map[tag]
        rebuilt = assembled["regions"][tag]
        expected = set(parent["regions"][original])
        assert rebuilt == expected, "reassembly changed exact support"
        exact_rows.append({"tag": list(tag), "parent_index": original,
                           "reassembled_support": sorted(rebuilt), "parent_support": sorted(expected)})
    mapped_boundary = index_map[assembled["boundary"]] if assembled["boundary"] is not None else None
    assert mapped_boundary == boundary, "boundary index map mismatch"
    assert assembled_report["cost"] == parent_report["cost"]
    summary = {
        "kind": kind,
        "left_regions": children[0]["regions"], "right_regions": children[1]["regions"],
        "left_boundary": children[0]["boundary"], "right_boundary": children[1]["boundary"],
        "parent_count": parent_report["count"], "parent_cost": parent_report["cost"],
        "left_count": child_reports[0]["count"], "right_count": child_reports[1]["count"],
        "left_cost": child_reports[0]["cost"], "right_cost": child_reports[1]["cost"], "toll": toll,
    }
    return {"summary": summary, "parent": parent_report, "children": children,
            "child_reports": child_reports, "live_indices": live, "open_branch_live": premise,
            "overlap": sorted(overlap), "parent_boundary_live_flags": flags,
            "count_equation": {"lhs": sum(c["count"] for c in child_reports),
                               "rhs": parent_report["count"] + int(all(flags))},
            "cost_equation": {"lhs": parent_report["cost"],
                              "rhs": sum(c["cost"] for c in child_reports) + toll},
            "index_bijection": exact_rows, "mapped_boundary": mapped_boundary,
            "exact_reassembly": True}


def numeric_equal(actual, claimed):
    return actual == claimed  # NUMERIC_COMPARISON_MUTATION_SITE


def compare_claim(actual, claimed):
    """Exact comparator; numeric mutation is confined to a copied module."""
    mismatches = []
    if set(actual) != set(claimed):
        mismatches.append({"field": "schema", "actual": sorted(actual), "claimed": sorted(claimed)})
    for field in sorted(set(actual) & set(claimed)):
        a, b = actual[field], claimed[field]
        if type(a) is int:
            same = type(b) is int and numeric_equal(a, b)
        elif field.endswith("_regions"):
            same = set(a) == set(b) and all(set(a[i]) == set(b[i]) for i in a)
        else:
            same = a == b
        if not same:
            mismatches.append({"field": field, "actual": a, "claimed": b})
    return {"accepted": not mismatches, "mismatches": mismatches}
