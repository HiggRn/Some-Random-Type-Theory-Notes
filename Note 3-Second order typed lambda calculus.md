# Note 3-Second order typed lambda calculus

[Simply typed $\lambda$ calculus](Note%202-Simply%20typed%20lambda%20calculus.md) talks about the system $\lambda\to$, whcih describes terms based on terms. Its abstraction level is restricted to terms, also known as first order dependency.

In this note, we'll further develop the level of abstraction and introduce the system called second order typed $\lambda$ calculus, denoted by $\lambda2$.

## Problem with $\lambda\to$

Consider an indentity function that takes $x$ (whatever the type) and simply return $x$.

We can't express such function in $\lambda\to$ system but to split it into different functions for each type of $x$, such as $\lambda x:Nat.x$.

We consider $*$ wo be the type of all types.

We want to extend the $\lambda\to$ system by adding another layer of abstraction.

Our first instinct for describing the identity function might be like this:
$$
\lambda\alpha:*.\lambda x:\alpha.x
$$

That is a good thought, but we'll run into a problem when considering the type of that identity function. Its type seems to be $*\to(\alpha\to\alpha)$, depending on the "bound" type paremeter $\alpha$, which is not what we desire.

## $\Pi$ binder

We describe the type of the identity function as $\Pi\alpha:*.\alpha\to\alpha$, which satisfies
$$
\Pi\alpha:*.\alpha\to\alpha=_\alpha\Pi\beta:*.\beta\to\beta
$$

thereby solving the problem with our naive extension of $\lambda\to$ system.

We now try another example-the type of function composition
$$
\circ:\Pi\alpha:*.\Pi\beta:*.\Pi\gamma:*.(\alpha\to\beta)\to(\beta\to\gamma)\to\alpha\to\gamma
$$

The introduction of $\Pi$ binder brings about the $\lambda2$ system. You can think of it as a means to  describe polymorphic functions.

## System $\lambda2$

$\lambda2$ and $\lambda\to$ are pretty similar, so I'm going to omit some straightforward things.

Still, we'll denote the set of all type variables as $\mathbb{V}$.

### Def(The set of $\lambda2$ types):

$$
\mathbb{T}2=\mathbb{V}|(\mathbb{T}2\to\mathbb{T}2)|(\Pi\mathbb{V}:*.\mathbb{T}2)
$$

### Def(The set of second order per-type $\lambda$ terms):

$$
\Lambda_{\mathbb{T}2}=V|(\Lambda_{\mathbb{T}2}\Lambda_{\mathbb{T}2})|(\Lambda_{\mathbb{T}2}\mathbb{T}2)|(\lambda V:\mathbb{T}2.\Lambda_{\mathbb{T}2})|(\lambda V:*.\Lambda_{\mathbb{T}2})
$$

- (Statement): 
    1. $M:\sigma,M\in\Lambda_{\mathbb{T}2},\sigma\in\mathbb{T}2$
    2. $\sigma:*,\sigma\in\mathbb{T}2$
- (Declaration):Statements like $x:\sigma$, where $x\in V$
- (Context): A bit more rigorous and therefore complicated
    1. $\empty$ is a $\lambda2$ context and $\mathtt{dom}(\empty)=()$.
    2. If $\Gamma$ is a $\lambda2$ context, $\alpha\in\mathbb{V}$ and $\alpha\notin\mathtt{dom}(\Gamma)$, then $\Gamma,\alpha:*$ is a $\lambda2$ context and $\mathtt{dom}(\Gamma,\alpha:*)=(\mathtt{dom}(\Gamma),\alpha)$.
    3. If $\Gamma$ is a $\lambda2$ context, $\rho\in\mathbb{T}2$ and $FV(\rho)\subseteq\mathtt{dom}(\Gamma)$, then $\Gamma,x:\rho$ is a $\lambda2$ context and $\mathtt{dom}(\Gamma,x:\rho)=(\mathtt{dom}(\Gamma),x)$.

Here $FV(\rho)$ denotes all free type variables in type $\rho$.

The definition of a context is a bit more complex than that in $\lambda\to$ since we can no longer use a type variable $\alpha$ before specifically stating $\alpha:*$.

Then we can give the derivation rules:
$$
\begin{array}{l}
    (var)\Gamma\vdash x:\sigma\text{ if } \Gamma\text{ is a }\lambda2\text{ context},x:\sigma\in\Gamma \\
    \\
    (appl)\dfrac{\Gamma\vdash M:\sigma\to\tau\quad\Gamma\vdash N:\sigma}{\Gamma\vdash MN:\tau} \\
    \\
    (abst)\dfrac{\Gamma,x:\sigma\vdash M:\tau}{\Gamma\vdash\lambda x:\sigma.M:\sigma\to\tau} \\
    \\
    (appl2)\dfrac{\Gamma\vdash M:\Pi\alpha:*.A\quad\Gamma\vdash B:*}{\Gamma\vdash MB:A[\alpha\coloneqq B]} \\
    \\
    (abst2)\dfrac{\Gamma,\alpha:*\vdash M:A}{\Gamma\vdash\lambda\alpha:*.M:\Pi\alpha:*.A} \\
    \\
    (form)\Gamma\vdash B:*\text{ if } \Gamma\text{ is a }\lambda2\text{ context},B\in\mathbb{T}2,FV(B)\subseteq\mathtt{dom}(\Gamma)
\end{array}
$$

The $(appl)$ and $(abst)$ rules are the same as those in $\lambda\to$.

### Def(Legal $\lambda2$ terms)

$M\in\Lambda_{\mathbb{T}2}$ is called a legal $\lambda2$ term if there exists a $\lambda2$ context $Gamma$ and a type $\rho\in\mathbb{T}2$ such that $\Gamma\vdash M:\rho$.

## Properties of $\lambda2$

### Def($\alpha$ conversion)

- $\lambda x:\sigma.M=_\alpha\lambda y:\sigma.M^{x\to y}$, if $y$ doesn't appear in $M$.
- $\lambda\alpha:*.M=_\alpha\lambda\beta:*.M[\alpha\coloneqq\beta],\Pi\alpha:*.M=_\alpha\Pi\beta:*.M[\alpha\coloneqq\beta]$, if $\beta$ doesn't appear in $M$.

Such $\alpha$ conversion also has compatibility, reflexivity, symmetry and transitivity, which are omiited in this note.

### Def(One-step $\beta$ reduction):

- $(\lambda x:\alpha.M)N\to_\beta M[x\coloneqq N]$
- $(\lambda\alpha:\alpha.M)T\to_\beta M[\alpha\coloneqq T]$

Similarly, comaptibility holds.

All the following theorems in $\lambda\to$ still hold and are omitted:

- Free Variables Lemma
- Thinning Lemma
- Condensing Lemma
- Generation Lemma
- Subterm Lemma
- Uniqueness of Types
- Substitution Lemma
- Church-Rosser Theorem
- Subject Reduction
- Termination Theorem

But the permutation lemma in $\lambda\to$ may not hold. It is no longer allowed to arbitrarily permute the declarations in a context Γ occurring in a judgement $\Gamma\vdash M:T$, since a declaration occurring later in that context may *depend* on an earlier one.

This $\lambda2$ system is also referred to as "system F".

****

## Exercise

1. Find terms in $\Lambda_{\mathbb{T}2}$ that have the following types, each in the given context $\Gamma$:
   1. $\Pi\delta:*.((\alpha\to\gamma)\to\delta)\to(\alpha\to\beta)\to(\beta\to\gamma)\to\delta$ where $\Gamma\equiv\alpha:*,\beta:*,\gamma:*$
   2. $\Pi\alpha,\beta,\gamma:*.(\alpha\to(\beta\to\alpha)\to\gamma)\to\alpha\to\gamma$ where $\Gamma\equiv\empty$
