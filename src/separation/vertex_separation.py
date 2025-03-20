
"""Use the MILP formulation given in
  https://doc.sagemath.org/html/en/reference/graphs/sage/graphs/graph_decompositions/vertex_separation.html

  Note: According to the paper of Kinnersley
  (https://www.sciencedirect.com/science/article/abs/pii/002001909290234M)
  'The vertex separation number of a graph equals its path-width'
  Information Processing Letters
  Volume 42, Issue 6, 24 July 1992, Pages 345-350

  V_L(i) is the number of vertices of G mapped to integers <= i that are adjacent
  to integer greater than i.

  In the model below this is reversed: V_L(i) is the number of vertices of G that
  mapped to integers > i that are adjacent to vertices <= i.  This seems to be the reverse

  This model is due to David Coudert
  https://www-sop.inria.fr/members/David.Coudert/code/graph-linear-ordering.shtml
  rendered as a MaxSat Problem using RC2.

  We describe below a mixed integer linear program (MILP) for
  determining an optimal layout for the vertex separation of G, which
  is an improved version of the formulation proposed in [SP2010]. It
  aims at building a sequence S[t] of sets such that an ordering of
  the vertices correspond to S[1] = {v[1]}, S[2] = {v[1], v[2]}, ...,
  S[n] = {v[1], ..., v[n]}.

  My comment: Let U[t] denote the subset of nodes which are not in S[t]
  but have a neighbor in S[t]

  X[t] = S[t] union U[t]

  Requirement #S[t] = t
  S[t] subset S[t+1]
  X[t] = neighbors(S[t])
  so X[t+1] = X[t] union {v[t]} union neighbor({v[t]})

  does U[t] = X[t] difference S[t]?

  i.e. u[v,t] = ~y[v,t] AND x[v,t]
  or y[v,t] OR ~x[v,t] OR u[v,t] is true.
  and ~u[v,t] OR ~y[v,t], ~u[v,t] OR x[v,t]

  But, according to Kinnersley we should have
     U[t] = { v in S[t] AND exists w not in S[t] for w in neighbors(v)}
  So u[v,t] = y[v,t] AND (OR (~y[w,t] for w in neighbors(v)))
  Since u is bounded from above we only need one direction:

  ~y[v,t] OR (~ (OR (~y[w,t] for w in neighbors(v)))) OR u[v,t]


  ~y[v,t] OR u[v,t] Or y[w,t] for all w in neighbors(v)

  If w is not in S[t] and v is in S[t] then u[v,t] is true
  If w is in S[t] or v is not in S[t] then no condition on u[v,t]
  
  In the other direction:
  ~u[v,t] OR (y[v,t] AND (OR (~y[w,t] w in nbr(v)))) <==>
  ~u[v,t] OR y[v,t]
  ~u[v,t] OR OR(~y[w,t] for w in nbr(v))
  
  So u[v,t] = y[v,t] AND ~x[v,t]
  So we have

  ~y[v,t] OR x[v,t] OR u[v,t]
  ~u[v,t] OR y[v,t]
  ~u[v,t] OR ~x[v,t]
  
  Variables:

  . y[v,t] – variable set to 1 if v in S[t], and 0 otherwise. The order
  of v in the layout is the smallest t such that y[v,t] = 1

  . u[v,t] – variable set to 1 if v not in S[t] and has an in-neighbor
  in S[t]. It is set to 0 otherwise. [u is "bad" at time t if it doesn't
  occur by time t, but has a neighbor that does]

  . x[v,t] – variable set to 1 if either v in S[t] or if v has an
  in-neighbor in S[t]. It is set to 0 otherwise.

  . z – objective value to minimize. It is equal to the maximum over
  all step t of the number of vertices such that u[v,t] = 1.

  MILP formulation:

  Minimize: z
  Such that:
  x[v,t] <= x[v,t+1] for v in V, 0 <= t <= n-2
  y[v,t] <= y[v,t+1] for v in V, 0 <= t <= n-2
  y[v,t] <= x[w,t] for v in V, w in N+(v), 0 <= t <=n-1
  sum(v in V) y[v,t] = t+1 for 0<= t <= n-1
  x[v,t] - y[v,t] <= u[v,t] for v in V, 0<=t <= n-1
  sum(v in V) u[v,t] <= z for 0<=t <= n-1
  0 <= x[v,t] <=1 for v in V, 0 <=t <= n-1
  0 <= u[v,t] <=1 for v in V, 0 <=t <= n-1
  y[v,t] in {0,1}
  0 <= z <= n

  Rewrite for undirected graphs
  y[w,t] => x[v,t] for all w in nbr(v)
  x[v,t] => y[w',t] OR u[w',t] for all w' in nbr(v)

  So it looks like this amounts to
  y[w,t] => y[w',t] OR u[w',t] for all w != w' in nbr(v)

  Starting from the definition of u[v,t]

  u[v,t] <==> (~y[v,t]) AND (OR[w in nbr(v)] y[w,t])

  This amounts to

  u[v,t] => ~y[v,t]
  ~u[v,t] OR (OR[w in nbr(v)] y[w,t])

  (y[v,t] OR (AND[w in nbr(v)] ~y[w,t]) OR u[v,t]

  Expanding by distributivity:

  y[v,t] OR ~y[w,t] OR u[v,t] for all w in nbr(v)

  Since we are upper bounding the sum of u[v,t] we only need the latter.

  The vertex separation of G is given by the value of z, and the order
  of vertex v in the optimal layout is given by the smallest t for
  which y[v,t] = 1.

  Note that this is for directed graphs, N+(v) is the out neighborhood of v

"""
from typing import Dict, Hashable, Tuple, List
from itertools import product, chain
import networkx as nx
from pysat.formula import IDPool, WCNF, CNF
from pysat.examples.rc2 import RC2, RC2Stratified
from pysat.card import CardEnc, EncType

class VertexSeparation:

    def __init__(self, gph: nx.Graph | nx.DiGraph,
                 verbose: int  = 0,
                 trace: int = 0,
                 bound: int | None = None,
                 # limit: int | None = None,
                 encode='totalizer'):

        self._graph = gph
        self._pool = IDPool()
        self._cnf = WCNF() if bound is None else CNF()
        self._size = len(self._graph.nodes)
        self._nbr = self._graph.neighbors if isinstance(gph, nx.Graph) else self._graph.predecessors
        # encoding for general cardinality constraints
        self._encode = getattr(EncType, encode, EncType.totalizer)
        # limit is an upper bound on the pathwidth.
        #self._limit = self._size if limit is None else limit
        self._limit = self._size
        self._bound = bound
        self._verbose = verbose
        self._trace = trace
        self._model()
        if self._verbose > 0:
            clause_info = (len(self._cnf.clauses) if bound is not None
                else (len(self._cnf.hard), len(self._cnf.soft)))
            print("Created the model with {clause_info} clauses")

    @property
    def clauses(self):

        return self._cnf.hard if self._bound is None else self._cnf.clauses
        
    def _model(self):
        # Hard constraints
        # #   x[v,t] <= x[v,t+1] for v in V, 1 <= t <= n-1
        # self._cnf.extend([
        #     [-self._pool.id(('x', _)), self._pool.id(('x', _[0], _[1] + 1))]
        #     for _ in product(self._graph.nodes, range(1, self._limit))])
        #   y[v,t] <= x[v,t] for v in V, 1 <= t <= n-1
        # self._cnf.extend([
        #     [-self._pool.id(('y', _)), self._pool.id(('x', _))]
        #     for _ in product(self._graph.nodes, range(1, self._limit + 1))])
        #   y[v,t] <= y[v,t+1] for v in V, 1 <= t <= n-1

        # Every node v is allocated to a unique time t
        # The pathwidith of that allocation is the maximum distance
        # between neighbors.
        # There are three families of variables
        # 1) y[v,t]: True if vertex v occurs in the path at time <= t
        # 2) u[v,t]: True if vertex v occurs in the path at time > t and has a neighbor at time <= t
        # 3) z[t]: Used for upper bounding successive sums of u[v,t]
        # (v occurs at time <= t) => (v occurs at time <= t+1)
        self._cnf.extend([
            [-self._pool.id(('y', _)), self._pool.id(('y', (_[0], _[1] + 1)))]
            for _ in product(self._graph.nodes, range(1, self._limit))])
                
        # #   y[v,t] <= x[w,t] for v in V, w in N+(v), 1 <= t <=n
        # self._cnf.extend([
        #     [-self._pool.id(('y', _)), self._pool.id(('x', (nbr, _[1])))]
        #     for _ in product(self._graph.nodes, range(1, self._limit + 1))
        #     for nbr in nx.neighbors(self._graph, _[0])])
        # z non-increasing
        if self._bound is None:
            self._cnf.extend([[self._pool.id(('z', _)), -self._pool.id(('z', _ + 1))]
                              for _ in range(1, self._limit)])
            zneg = [-self._pool.id(('z', _)) for _ in range(1, self._limit + 1)]
            self._cnf.extend([[-self._pool.id(('z', _))] for for _ in range(1, self._limit + 1)],
                             weights = self._limit * [1])
                
        # (v occurs at time <= t) => (w occurs at time > t) OR (w occurs at time <= t)
        # where w is a neighbor of v
        for tme in range(1, self._limit + 1):
            if self._trace > 0 and (tme % self._trace == 0):
                print(f"Created {len(self.clauses)} clauses at time {tme}")
            self._cnf.extend([
                [-self._pool.id(('y', (node, tme))),
                 # self._pool.id(('u', (nbr, tme))),
                 self._pool.id(('u', (node, tme))),
                 self._pool.id(('y', (nbr, tme)))]
                for node in self._graph.nodes
                for nbr in self._nbr(node)])

            # Objective to be minimized
            # Objective = sum_t z[t] to be minimized: take complement for maxsat
            #   sum(v in V) y[v,t] = t for 1 <= t <= n
            # Exactly t nodes are allocated from 1 to t
            ylits = [self._pool.id(('y', (_, tme))) for _ in self._graph.nodes]
            self._cnf.extend(CardEnc.equals(lits = ylits,
                                            bound = tme,
                                            encoding = self._encode,
                                            vpool = self._pool))
            # sum_t z[t] >= sum_v u[v,t_0]: left hand sum is an upper bound
            ulits = [self._pool.id(('u', (_, tme))) for _ in self._graph.nodes]
            #   sum(v in V) u[v,t] <= z for 1 <= t <= n
            if self._bound is None: # We are minimizing
                bnd = self._limit
                xlits = ulits + zneg
            else: # We are looking for feasibility for a bound
                bnd = self._bound
                xlits = ulits
            self._cnf.extend(CardEnc.atmost(lits = xlits,
                                            bound = bnd,
                                            encoding = self._encode,
                                            vpool = self._pool))
        #   x[v,t] - y[v,t] <= u[v,t] for v in V, 1 <= t <= n
        # self._cnf.extend([
        #     [self._pool.id(('y', _)), self._pool.id(('u', _)), - self._pool.id(('x', _))]
        #     for _ in product(self._graph.nodes, range(1, self._limit + 1))])
        #   x[v,t] - y[v,t] <= u[v,t] for v in V, 1 <= t <= n
        # self._cnf.extend([
        #     [- self._pool.id(('y', _)), self._pool.id(('u', _)), self._pool.id(('x', _))]
        #     for _ in product(self._graph.nodes, range(1, self._limit + 1))])


    def solve(self,
              solver = 'cd195',
              stratified: bool = False,
              **kwds) -> Tuple[int, Dict[Hashable, int]]:
        if self._bound is None:
            maxsat_solver = RC2Stratified if stratified else RC2
            print(f"{'' if stratified else 'un'}stratified")
            max_solver = maxsat_solver(self._cnf, solver = solver, verbose = verbose, **kwds)
            soln = max_solver.compute()
            if kwds.get('verbose', 0) > 0:
                print(f"Time = {max_solver.oracle_time()}")
        else: # Use ordinary SAT
            mysolver = Solver(name = solver,
                bootstrap_with = self._cnf,
                use_timer = True)
            soln = mysolver.solver()
            if kwds.get('verbose', 0) > 0:
                print(f"Time = {mysolver.time()}")
            
        pos = [self._pool.obj(_) for _ in soln if _ > 0]
        if self._bound is None:
            mylen = len([_[1] for _ in pos
                if _ is not None and _[0] == 'z'])
        else:
            mylen = self._bound
        yvals = {_[1] for _ in pos if _ is not None and _[0] == 'y'}

        yorder = {node: min((_[1] for _ in yvals if _[0] == node))
            for node in self._graph.nodes}
        return mylen, yorder
        
def pathwidth_order(gph: nx.Graph | nx.DiGraph,
                    bound: int | None = None,
                    **kwds) -> Tuple[int, List[Hashable]]:

    """
      Produce a renumbered graph by means of optimal pathwidth (the
      same as vertex separation order).
    """

    vsp = VertexSeparation(gph, bound = bound)
    sep, renumber = vsp.solve(**kwds)
    return sep, [_[0] for _ in sorted(renumber.items(), key=lambda _: _[1])]

def separation(gph: nx.Graph | nx.DiGraph) -> int:

    snodes = sorted(gph.nodes)
    nbr = gph.neighbors if isinstance(gph, nx.Graph) else gph.predecessors
    val = 0
    # Calculate V_L(i)
    for ind in range(len(gph.nodes)):
        tnodes = set(snodes[: ind + 1])
        bad = {node for node in tnodes
            if not set(nbr(node)).issubset(tnodes)}
        val = max(len(bad), val)
    return val

def alt_separation(gph: nx.Graph | nx.DiGraph) -> int:

    snodes = sorted(gph.nodes)
    nbr = gph.neighbors if isinstance(gph, nx.Graph) else gph.predecessors

    val = 0
    # Calculate V_L(i)
    for ind in range(len(gph.nodes)):
        tnodes = set(snodes[: ind + 1])
        bad = set(chain(*(set(nbr(node)).difference(tnodes)
                        for node in tnodes)))
        val = max(len(bad), val)
    return val
