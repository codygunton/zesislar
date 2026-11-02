"""Compute dependency closure without importing preparation-only modules."""


def graph_closure(seeds, graph):
    found, pending = set(seeds), list(seeds)
    while pending:
        for name in graph.get(pending.pop(), ()):
            if name not in found:
                found.add(name)
                pending.append(name)
    return found
