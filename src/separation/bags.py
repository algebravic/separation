"""
  Find a bag decomposition of a graph given an elimination order.

  
"""
from typing import Hashable, Tuple, Iterable
from itertools import combinations
import networkx as nx

def bag_decomposition(gph: nx.Graph, order: Iterable[Hashable]) -> nx.Graph:

    # Check that the input is compatible
    gnodes = frozenset(gph.nodes)
    onodes = frozenset(order)
    if gnodes != onodes:
        raise ValueError("The order list is not the set of nodes")

    ngph = gph.copy()
    bags = {}
    for ind, node in enumerate(order):

        nbrs = ngph.neighbors(node)
        bags[node] = frozenset([node]).union(set(order[ind + 1:]).intersection(nbrs))
        ngph.remove(node)

        # Make the neighbors a clique
        ngph.add_edges_from(combinations(nbrs, 2))


    # Now create the tree
    tgph = nx.Graph()

    for ind, node in enumerate(order):

        # Find the bag that share the most vertices with it.
        tbag = bags[node]
        cand = max(order[ind + 1:],
                   default = None,
                   key = lambda _: len(tbag.intersection(bags[_])))
        if cand is not None and tbag.intersection(bags[cand]):
            tgph.add_edge(tbag, bags[cand])

    return tgph
