Path Width Ordering
===================

Let $G$ be an undirected graph with $n$ vertices. An ordering, $f$ is
a one to one map $f: V(G) \rightarrow [n]$, where $[n]$ denotes the
set $\{1, \dots, n\}$. The *width* of $f$ is defined to be
$\max_{(v,w) \in E(G)} |f(v) - f(w)|$. The *path width* of $G$ is the
width of that ordering $f$ which attains the minimum over all possible
orderings.

There is a similar definition for directed graphs.

One can calculate this via an integer program or a maxsat calculation.

We encode an ordering as follows: Let $x[v,t]$ be a boolean variable
which is true if $f(v) \le t$, and false otherwise. We must have the
following constraints: for $1 \le t < n$ $x[v,t] \Rightarrow
x[v,t+1]$, and for all $t \in [n]$, $\sum_{v \in V(G)} x[v,t] =
t$. The latter ensures that at time $t$ there are exactly $t$ vertices
that are allocated. We also have boolean variables $u[v,t]$ which is
true if and only if $f(v) > t$ and there is an edge $(v,w)$ so that
$f(w) \le t$.

Note the following for all $v \in V(G)$
$`\sum_t u[v,t] = \max_{w, f(w) < f(v), (v,w) \in E(G)} f(v) - f(w)`$
Suppose that $f(v) = t'$. If $v$ has no neighbor, $w$, with $f(w) <
f(v)$, then all of the $u[v,t]$ are false. Otherwise suppose that
$w = \arg\min \{ f(z): (z,v) \in E(G), f(z) < f(v)\}$. Then
$u[v,t]$ is false for $t < f(w)$, and for $t > f(v)$, but is true
for all other values, which are $f(v) - f(w)$ in number.

Thus if we add the integer constraints $`z \ge \sum_t u[v,t]`$ for all
$v \in V(G)$, and minimize $z$ we obtain the path width.

In order to obtain this as a maxsat problem define boolean variables
$z[t]$, and ask that we maximize the number of $z[t]$ to be true.
We then have the following constraints: $z[t] \Rightarrow z[t+1]$ for
$1 \le t < n$, and $`\sum_t (u[v,t] + \overline{z[t]}) \le n`$, where
$\overline{z[t]}$ denote the negation.

Finally, since we are minimizing an upper bound on $`\sum_t u[v,t]`$
we only need the constraint $f(v) > t \& (\exists_{(v,w) \in E(G)}
f(w) \le t) \Rightarrow u[v,t]$. This is now the same as
$x[v,t] \vee (\bigwedge_{(v,w) \in E(G)} \overline{x[w,t]}) \vee
u[v,t]$. Expanding out by distributivity, this yields the following
constraints:

$x[v,t] \vee \overline{x[w,t]} \vee u[v,t]$ for all $(v,w) \in E(G)$.
