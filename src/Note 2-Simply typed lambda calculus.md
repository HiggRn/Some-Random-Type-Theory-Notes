# Note 2-Simply typed lambda calculus

[Untyped $\lambda$ calculus](Note%201-Untyped%20lambda%20calculus.md) is concisely defined, and yet it includes meaningless terms such as $xx$. We need to introduce types to further control functions' behaviors.

We introduce $\lambda\to$ in this note, and also proof trees(i.e. derivation system), which will be the basis of following notes. $\lambda2$, $\lambda\underline{\omega}$, and $\lambda P$ all extend from $\lambda\to$.

## Simple types

Let set $\mathbb{V}$ be the set of all simple type variables(e.g. $\alpha$,$\beta$).

### Def(The set of all simple types):
We use $\mathbb{T}$ to denote the set of all simple types, where
$$
\mathbb{T}=\mathbb{V}|\mathbb{T}\to\mathbb{T}
$$

That is:

- (type variable)$\alpha\in\mathbb{V}\implies\alpha\in\mathbb{T}$
- (arrow type)$\alpha,\beta\in\mathbb{V}\implies\alpha\to\beta\in\mathbb{T}$

We'll use $\alpha$, $\beta$ to denote members in $\mathbb{V}$, and use $\sigma$, $\gamma$ to denote members in $\mathbb{T}$.

$M:\sigma$ means that $M$ is of type $\sigma$.

So we have the relation of types in application and abstraction:

- (application)$M:\sigma\to\tau,N:\sigma\implies MN:\tau$
- (abstraction)$x:\sigma,M:\tau\implies\lambda x.M:\sigma\to\tau$

### Def(Pre-typed $\lambda$ terms):
$$
\Lambda_{\mathbb{T}}=V|\Lambda_{\mathbb{T}}\Lambda_{\mathbb{T}}|\lambda V:\mathbb{T}.\Lambda_{\mathbb{T}}
$$

Therefore it's clear to see that $xx$ can't be in $\Lambda_{\mathbb{T}}$.

## Derivation rules
We now give 4 quick definitions:

- (Statement) Expressions like $M:\sigma$, where $M\in\Lambda_{\mathbb{T}},\sigma\in\mathbb{T}$
- (Declaration) Statements like $x:\sigma$, where $x\in V$
- (Context) A series of declaration
- (Judgement) Expressions like $\Gamma\vdash M:\sigma$, where $\Gamma$ is a context

We now introduce the **derivation system**:
$$
\mathtt{premiss}_1\quad\mathtt{premiss}_2 \quad\mathtt{premiss}_3\over\mathtt{conclusion}
$$
which means that $\mathtt{premiss}_1,\mathtt{premiss}_2,\mathtt{premiss}_3$ can derive the $\mathtt{conclusion}$, also called the **proof tree**.

Now we'll give the derivation rules for $\lambda\to$ system.
$$
\begin{array}{l}
    (var)\Gamma\vdash x:\sigma ~~\text{if}~~x:\sigma\in\Gamma \\
    \\
    (appl)\dfrac{\Gamma\vdash M:\sigma\to\tau\quad\Gamma\vdash N:\sigma}{\Gamma\vdash MN:\tau} \\
    \\
    (abst)\dfrac{\Gamma,x:\sigma\vdash M:\tau}{\Gamma\vdash\lambda x:\sigma.M:\sigma\to\tau} \\
\end{array}
$$

Now we can infer the type of a certain term using these rules. An example goes like this:

$$
\dfrac{y:\alpha\to\beta,z:\alpha\vdash y:\alpha\to\beta\quad y:\alpha\to\beta,z:\alpha\vdash z:\alpha}{\dfrac{y:\alpha\to\beta,z:\alpha\vdash yz:\beta}{\dfrac{y:\alpha\to\beta\vdash\lambda z:\alpha.yz:\alpha\to\beta}{\empty\vdash\lambda y:\alpha\to\beta.\lambda z:\alpha.yz:(\alpha\to\beta)\to\alpha\to\beta}}}
$$

***NOTE**: In the three derivation rules, only $(var)$ can appear in the top of a proof tree.

### Def(Legal $\lambda\to$ term):
We say that a pre-typed term $M$ in $\lambda\to$ system is a legal $\lambda\to$ term, if there exist context $\Gamma$ and type $\rho$, such that $\Gamma\vdash M:\rho$.

## Typability, type checking and term finding

There are generally three kinds of problems we cared about in a type system.

1. Typability: Given a term $M$, we need to judge whether it's legal by finding a context $\Gamma$ and a type $\rho$ such that $\Gamma\vdash M:\rho$.
2. Type checking: Given a statement $\Gamma\vdash M:\rho$, we want to check whether it's true.
3. Term finding: Given a context $\Gamma$ and a type $\rho$, we want to find a term $M$ such that $\Gamma\vdash M:\rho$.

It can be proved that these three kinds of problems can always be solved in $\lambda\to$ system.

## Properties of $\lambda\to$ system

We'll start by giving some definitions:

- If $\Gamma\equiv x_1:\sigma_1,\cdots,x_n:\sigma_n$, then the domain of $\Gamma$, namely $\mathtt{dom}(\Gamma)=\{x_1,\cdots,x_n\}$.
- If all the declarations in $\Gamma'$ appear in $\Gamma$ in the same order, then we say $\Gamma'\subseteq\Gamma$.
- If all variables in $\Gamma'$ appear in $\Gamma$, then we say that $\Gamma'$ is a permutation of $\Gamma$.
- The projection of $\Gamma$ on a varable set $\Phi$, denoted by $\Gamma\upharpoonright\Phi$, is the context that only contains the declarations in $\Gamma$ whose variables are in $\Phi$

For instance, 
$$\Gamma\equiv x_1:\sigma_1,x_2:\sigma_2,x_3:\sigma_3,\Phi=\{x_1,x_2,x_4\}\implies\Gamma\upharpoonright\Phi\equiv x_1:\sigma_1,x_2:\sigma_2
$$

Now we can discuss $\lambda\to$ system's properties.

### Lemma(Free Variables Lemma):
$$
\Gamma\vdash L:\sigma\implies FV(L)\subseteq\mathtt{dom}(\Gamma)
$$

### Lemma(Thinning Lemma):
$$
\Gamma'\subseteq\Gamma'',\Gamma'\vdash M:\sigma\implies\Gamma''\vdash M:\sigma
$$

### Lemma(Condensing Lemma):
$$
\Gamma\vdash M:\sigma\implies\Gamma\upharpoonright FV(M)\vdash M:\sigma
$$

### Lemma(Permutation Lemma):
Suppose $\Gamma'$ is a permutation of $\Gamma$, then
$$
\Gamma\vdash M:\sigma\implies\Gamma'\vdash M:\sigma
$$

### Lemma(Generation Lemma):
$$
\begin{array}{l}
    \Gamma\vdash x:\sigma\implies x:\sigma\in\Gamma \\
    \Gamma\vdash MN:\tau\implies\exists\sigma\in\mathbb{T}~~s.t.~~\Gamma\vdash M:\sigma\to\tau,N:\tau \\
    \Gamma\vdash\lambda x:\sigma.M:\rho\implies\exists\tau\in\mathbb{T}~~s.t.~~\Gamma,x:\sigma\vdash M:\tau,\rho\equiv\sigma\to\tau
\end{array}
$$

This generation lemma explains how a judgement is constructed.

### Lemma(Subterm Lemma):
If $M$ is a legal $\lambda\to$ term, then all subterms of $M$ are legal $\lambda\to$ terms.

### Property(Uniqueness of Types):
$$
\Gamma\vdash M:\sigma,\Gamma\vdash M:\tau\implies\sigma\equiv\tau
$$

## $\beta$ ruduction in $\lambda\to$

So what are the properties of $\beta$ reduction in $\lambda\to$ system?

### Lemma(Substitution Lemma):
$$
\Gamma',x:\sigma,\Gamma''\vdash M:\tau\quad\Gamma'\vdash N:\sigma\implies\Gamma',\Gamma''\vdash M[x\coloneqq N]:\tau
$$

This lemma enables us to define one-step $\beta$ reduction in a similar way as in [Untyped $\lambda$ calculus](Note%201-Untyped%20lambda%20calculus.md).

### Def(One-step $\beta$ reduction):
$(\lambda x:\sigma.M)N\rightarrow_\beta M[x\coloneqq N]$

The definition of $\beta$ reduction is identical to that in [Untyped $\lambda$ calculus](Note%201-Untyped%20lambda%20calculus.md), and is omitted here.

Most importantly, the Church-Rosser Theorem still holds.

### Theorem(Church, Rosser):
For $M\in\Lambda_{\mathbb{T}}$, if $M\twoheadrightarrow_\beta N_1$, $M\twoheadrightarrow_\beta N_2$, then $\exists N_3$, such that $N_1\twoheadrightarrow_\beta N_2$,$N_2\twoheadrightarrow_\beta N_3$.

### Property(Subject reduction):
$$
\Gamma\vdash L:\rho,L\twoheadrightarrow_\beta L'\implies\Gamma\vdash L':\rho
$$

At last, we get what we introduce types for: strong normalization for every term.

### Theorem(Termination Theorem):
Every legal $\lambda\to$ term is strongly normalizing.

****
## Exercise

1. For each of the following terms, try to find a pre-typed variant which is typable. If this is not possible, show why.
    1. $\lambda x.\lambda y.x(\lambda z.y)y$
    2. $\lambda x.\lambda y.x(\lambda z.x)y$
2. Construct a term of type $((\alpha\to\beta)\to\alpha)\to(\alpha\to\alpha\to\beta)\to\alpha$.
3. Construct a term of type $((\alpha\to\beta)\to\alpha)\to(\alpha\to\alpha\to\beta)\to\beta$.
