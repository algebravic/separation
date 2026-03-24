"""
  Find a bag decomposition of a graph given an elimination order.

  
"""
from typing import Hashable, Tuple, Iterable
from itertools import combinations, islice
import networkx as nx

def bag_decomposition(gph: nx.Graph, order: Iterable[Hashable],
                      maximal: bool = False,
                      verbose: bool = False) -> nx.Graph:
    """
      Given an undirected graph, G, and an ordering of its vertices
      create the tree decomposition of the graph.

      The tree decomposition of G, is a tree whose nodes are labeled
      by subsets of the nodes of G, called 'bags'.

      This is a method that was given by Google Gemini.

      Question: It should be the case that if G is connected then T(G) is
      connected, yet this algorithm doesn't do that.

      
    """

    # Check that the input is compatible
    gnodes = frozenset(gph.nodes)
    onodes = frozenset(order)
    if gnodes != onodes:
        raise ValueError("The order list is not the set of nodes")

    ngph = gph.copy()
    bags = {}
    norder = order.copy()
    for node in norder:

        nbrs = list(ngph.neighbors(node))
        if verbose:
            print(f"{node} -> {nbrs}")
        ngph.remove_node(node)
        # The bag for this node is the node plus all of its neighbors
        # which are 'in the future'
        # This shouldn't be necessary, since we've removed all nodes
        # before the current one
        # extra = set(norder).intersection(nbrs)
        if nbrs:
            bags[node] = frozenset([node]).union(nbrs)

        # Make the future neighbors a clique
        ngph.add_edges_from(combinations(nbrs, 2))


    # Now create the tree
    tgph = nx.Graph()

    norder = order.copy()
    while norder:
        node = norder[0]
        norder = norder[1:]

        # Find the bag in the future that share the most vertices with it.
        if node in bags:
            tbag = bags[node]
            if len(tbag) == 1:
                print(f"{node} is alone!")
            cands = (_ for _ in norder if _ in bags and tbag.intersection(bags[_]))
            try:
                cand = (max(cands,
                            default = None,
                           key = lambda _: len(tbag.intersection(bags[_])))
                        if maximal else next(cands))
                if cand is not None:
                    tgph.add_edge(tbag, bags[cand])
            except StopIteration:
                pass # con't do anything
        else:
            print(f"The node {node} only has back edges.")

    return tgph
