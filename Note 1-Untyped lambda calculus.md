# Note 1-Untyped lambda calculus

## Basics

Let set $V$ be the set of all variables(e.g. $x$,$y$,$z$).

### Def($\lambda$ term):
The set of all $\lambda$ terms is denoted by $\Lambda$, where
$$
\Lambda = V | \Lambda\Lambda | \lambda V.\Lambda
$$

We use symbols $\equiv$ and $\not\equiv$ to represent whether two $\lambda$ terms are identical or not.

### Def(Subterm):
The set of all subterms of $M\in\Lambda$ is denoted by $\mathtt{Sub}(M)$, which is defined through the following rules:
1. $\mathtt{Sub}(x)=\{x\},\forall x\in V$
2. $\mathtt{Sub}(MN)=\mathtt{Sub}(M)\cup\mathtt{Sub}(N)\cup\{MN\},\forall M,N\in\Lambda$
3. $\mathtt{Sub}(\lambda x.M)=\mathtt{Sub}(M)\cup\{\lambda x.M\},\forall x\in V,\forall M\in\Lambda$

If $L$ is the subterm of $M$, and $L\not\equiv M$, then we say $L$ is the proper subterm of $M$.

## Free, binding and bound variables

In $\lambda x.xy$, the first $x$ is binding, the second $x$ is bound, and $y$ is free.

We use $FV(L)$ to denote all free variables in $L\in\Lambda$.

For instance,
$$
FV(\lambda x.xy)=\{y\}
$$

$$
FV(x\lambda x.xy)=\{x,y\}
$$

### Def(Closed $\lambda$ term):
$M\in\Lambda$ is a closed $\lambda$ term if $FV(M)=\empty$.

## $\alpha$ conversion

### Def($\alpha$ conversion):
$\lambda x.M=_\alpha\lambda y.M^{x\to y}$, i.e. swap all $x$ in $M$ to $y$

$\alpha$ conversion *only* applies with the criterion of $y\notin FV(M)$ and that $y$ is not a binding variable in $M$.

For instance:

- $(\lambda x.x(\lambda z.xy))z=_\alpha(\lambda u.u(\lambda z.uy))z$
- $(\lambda x.x(\lambda z.xy))z=_\alpha(\lambda z.z(\lambda x.zy))z$

$=_\alpha$ is referred to as $\alpha$ convertible.

We often consider $M\equiv N$ if $M=_\alpha N$.

There're some clear properties for $\alpha$ conversion:

- $M=_\alpha N\implies\begin{cases}
    ML&=_\alpha NL \\
    LM&=_\alpha LN \\
    \lambda z.M&=_\alpha\lambda z.N
\end{cases}$
- (reflexive)$M=_\alpha M$
- (symmetric)$M=_\alpha N\implies N=_\alpha M$
- (transitive)$M=_\alpha N,N=_\alpha L\implies L=_\alpha M$

## $\beta$ reduction

For substitution, we shall have some properties:

- $x[x\coloneqq N]\equiv N$
- $x\not\equiv y\implies y[x\coloneqq N]\equiv y$
- $(PQ)[x\coloneqq N]\equiv(P[x\coloneqq N])(Q[x\coloneqq N])$
- $\lambda y.P=_\alpha\lambda z.P^{y\to z},z\notin FV(N)\implies(\lambda y.P)[x\coloneqq N]\equiv\lambda z.(P^{y\to z}[x\coloneqq N])$
- $x\not\equiv y,x\notin FV(L)\implies M[x\coloneqq N][y\coloneqq L]\equiv M[y\coloneqq L][x\coloneqq N[y\coloneqq L]]$

### Def(One-step $\beta$ reduction):
$(\lambda x.M)N\rightarrow_\beta M[x\coloneqq N]$

Clearly we have some properties.

Suppose $M\rightarrow_\beta N$:

- $ML\rightarrow_\beta NL$
- $LM\rightarrow_\beta LN$
- $\lambda x.M\rightarrow_\beta\lambda x.N$

For instance, $(\lambda x.x(xy))N\rightarrow_\beta N(Ny)$.

### Def($\beta$ reduction):

We say that $M\twoheadrightarrow_\beta N$, if $\exist n\ge 0$, such that $M_0\equiv M, M_n\equiv N, M_i\rightarrow_\beta M_{i+1},\forall 0\le i\le n$.

Like $=_\alpha$, we can define $=_\beta$.

### Def($\beta$ convertible):

We say that $M=_\beta N$, if $\exist n\ge 0$, such that $M_0\equiv M, M_n\equiv N, M_i\rightarrow_\beta M_{i+1} or M_i\leftarrow_\beta M_{i+1},\forall 0\le i\le n$.

Just like $=_\alpha$, $=_\beta$ is also reflexive, transitive and symmetric.

## Normal forms

##### Def($\beta$ normal form):

- If $M\in\Lambda$ can't be $\beta$-reduced, we say $M$ is a $\beta$-normal form;
- If $M\twoheadrightarrow_\beta N$ and $N$ is a $\beta$-normal form, then we say that $N$ is the $\beta$-normal form of $M$, and call this process $\beta$-normalizing.

For example(**The following examples matters!!**),

- $(\lambda x.(\lambda y.yx)z)v\twoheadrightarrow_\beta zv$, and therefore $(\lambda x.(\lambda y.yx)z)v$ has a $\beta$-normal form.
- $\Omega\coloneqq(\lambda x.xx)(\lambda x.xx)$ doesn't have a $\beta$-normal form, for it always $\beta$-reduce to itself.
- Suppose $\Delta\coloneqq\lambda x.xxx$, then $\Delta\Delta\rightarrow_\beta\Delta\Delta\Delta\cdots$, therefore no $\beta$-normal form.

The process of $\beta$ reduction form a reduction path, which can be finite or infinite, even for a single $M\in\Lambda$, for instance, $(\lambda u.v)\Omega$.

We say that $M$ is weakly normalizing, if $\exists\beta$-normal form $N$, such that $M\twoheadrightarrow_\beta N$.

We say that $M$ is strongly normalizing, if all reduction paths of $M$ are finite.

Clearly, strongly normalizing $\implies$ weakly normalizing, and $(\lambda u.v)\Omega$ is an example of weakly normalizing but not strongly normalizing.

So the choice of reduction path matters.

### Theorem(Church, Rosser):
For $M\in\Lambda$, if $M\twoheadrightarrow_\beta N_1$, $M\twoheadrightarrow_\beta N_2$, then $\exists N_3$, such that $N_1\twoheadrightarrow_\beta N_2$,$N_2\twoheadrightarrow_\beta N_3$.

Therefore, we have the conclusion that if $M=_\beta N$, then $\exists L$, such that $M\twoheadrightarrow_\beta L$, $N\twoheadrightarrow_\beta L$.

## Fixed Point Theorem

### Theorem(Fixed Point Theorem):
$\forall L\in\Lambda$, $\exists M\in\Lambda$ such that $LM=_\beta M$.

There is a special closed $\lambda$ term, which always returns the fixed point of a given $\lambda$ term. It's called *Y-combinator*.

$$
Y\equiv\lambda f.(\lambda x.f(xx))(\lambda x.f(xx))
$$

We have:

$$
L(YL)=_\beta YL,\forall L\in\Lambda
$$

Proof is easy and omitted.

****
## Exercise

1. Prove that $\lambda x.x(\lambda z.y)=_\alpha\lambda z.z(\lambda z.y)$.
2. $M\in\Lambda$ has a $\beta$-normal form and an infinite reduction path:$M\equiv M_0\rightarrow_\beta M_1\rightarrow_\beta M_2\rightarrow_\beta\cdots$.
    1. Show that: every $M_i$ has a $\beta$-normal form.
    2. Give an example of such $M$.
