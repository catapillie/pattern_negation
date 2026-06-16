#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/showybox:2.0.4": showybox

#let ocaml = smallcaps([OCaml])

= Typed pattern-matching and pattern negation

== Notations

We consider $cal(C)$ an infinite set of constructors, which all have a fixed arity $k >= 0$.

$
  #text[*pattern*] p & := omega                    &                  #h(1cm) "wildcard" \
                     & #h(.5em) | C(p_1, ..., p_k) & #h(2cm) "constructor" C in cal(C)_v \
                     & #h(.5em) | p or q           &               #h(2cm) "disjunction" \
                     & #h(.5em) | p and q          &               #h(2cm) "conjunction" \
                     & #h(.5em) | not p            &                  #h(2cm) "negation" \
                     \
    #text[*value*] v & := C(p_1, ..., p_k)         & #h(2cm) "constructor" C in cal(C)_v \
$

We will work with a set $cal(T)$ of simples types. For any type $tau$, we claim to know its _signature_ $"sig" tau$, which is a set of constructors each equipped with a finite list of type arguments.
$ "sig" tau = { (C_1 "of" tau_11, ..., tau_(1 n_i)), (C_2 "of" tau_21, ..., tau_(2 n_2)), ... } $

Note that it is allowed
- for types to have an empty signature;
- for constructors to have no type arguments;
- for signatures to be infinite.

To simplify things a little with no loss of generality, we disallow the same constructor to appear twice in $"sig" tau$ with different type arguments. This assumption is entirely justified for if we have $(A "of" alpha)$ and $(A "of" beta)$ both in $"sig" tau$, then we can rewrite the second $A$ as a fresh constructor $A'$.

*Examples* Common types in #ocaml :
- $"sig" #raw("bool") = { #raw("false"), #raw("true") }$
- $"sig" (#raw("option") alpha) = { #raw("None"), #raw("Some") "of" alpha }$
- $"sig" #raw("empty") = diameter$
- $"sig" #raw("int") = ZZ$

*Definition* A value $v$ is of type $tau$, written $v:tau$, according the following rule.

#showybox[
  *$v:tau$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v_1 : tau_1$,
        $dots.c$,
        $v_n : tau_n$,
        $(A "of" tau_1, ..., tau_n) in "sig" tau$,
        $A(v_1, ..., v_n) : tau$,
      )),
    ),
  )
]

*Definition* $V(tau) = {v | v : tau}$ is the set of values of type $tau$. We say _$tau$ is empty_ iff $V(tau) = diameter$.

*Observation* A type whose signature is empty is also empty. Indeed, if $"sig" tau = diameter$ the then rightmost premise in the above rule is never satisfied, making a judgment of the form $v : tau$ impossible to derive.

== Rows and matrices

#let row(x) = $arrow(#x)$
#let unit = $mat()$
#let omegas(n) = $row(omega)^#n$

Later it will be useful to consider multiple patterns at once, for instance when we unwrap a pattern $C(p_1, ..., p_n)$ to only its arguments $p_1, ..., p_n$ and we need need to matches $n$ values $v_1, ..., v_n$ to the $p_i$'s all at once. In order to do so, we introduce more generally _rows of values_, _patterns_ and _types_, which will be denoted with an arrow :
$ row(tau) = mat(t_1, dots.c, t_n) #h(1cm) row(p) = mat(p_1, dots.c, p_n) #h(1cm) row(v) = mat(v_1, dots.c, v_n) $

Note that rows are allowed to be empty, and we will write them as unit rows : $unit$. We also see singleton rows $row(tau) = mat(tau_1)$ simply as the inner type $tau_1$, so that we are able to give general definitions over patterns and rows simultaneously. A constructor in a signature $(A "of" tau_1, ..., tau_n)$ can now for example be rewritten simply as $(A "of" row(tau))$, and a constructor pattern $A(p_1, ..., p_n)$ can be rewritten as $A(row(p))$, and so on. We will also write $omegas(n) = (omega, ..., omega)$ the row with $n$ wildcard patterns.

Intuitively, a row of $n$ patterns allows to match $n$ values at the same time without having to use a constructor of arity $n$.

In addition, we consider _matrices of patterns_ which can appear under multiple forms $ bold(P) = mat(p_(1 1), dots.c, p_(1 n); dots.v, dots.down, dots.v; p_(m 1), dots.c, p_(m n)) = mat(row(p)_1; dots.v; row(p)_m) $
Pattern matrices of height 1 can be seen as a single row. The _empty matrix_, i.e. the matrix with no rows, is written $diameter$.

== Typed pattern-matching

#let matches = $in$
#let mismatches = $in.not$

We now consider _typed pattern-matching_ as a relation between values, patterns and types, and similarly between rows of the same objects. A value _$v$ matches $p$ with type $tau$_, written $v matches p : tau$, whenever we can derive such a judgment from the following rules :

#showybox[
  *$v matches p : tau$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v : tau$,
        $v matches omega : tau$,
      )),
      prooftree(rule(
        $row(v) matches row(p) : row(alpha)$,
        $(A "of" row(alpha)) in "sig" tau$,
        $A(row(v)) matches A(row(p)) : tau$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v matches p_1 : tau$,
        $v matches p_1 or p_2 : tau$,
      )),
      prooftree(rule(
        $v matches p_2 : tau$,
        $v matches p_1 or p_2 : tau$,
      )),
      prooftree(rule(
        $v matches p_1 : tau$,
        $v matches p_2 : tau$,
        $v matches p_1 or p_2 : tau$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $exists i, v_i matches not p_i : tau_i$,
        $(A "of" tau_1, ..., tau_n) in "sig" tau$,
        $A(v_1, ..., v_n) matches not A(p_1, ..., p_n) : tau$,
      )),
      prooftree(rule(
        $A != B$,
        $A, B in "sig" tau$,
        $B(v_1, ..., v_m) matches not A(p_1, ..., p_n) : tau$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v matches not p_1 : tau$,
        $v matches not p_2 : tau$,
        $v matches not(p_1 or p_2) : tau$,
      )),
      prooftree(rule(
        $v matches not p_1 : tau$,
        $v matches not(p_1 and p_2) : tau$,
      )),
      prooftree(rule(
        $v matches not p_2 : tau$,
        $v matches not(p_1 and p_2) : tau$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v matches p : tau$,
        $v matches not not p : tau$,
      )),
    ),
  )

  *$row(v) matches row(p) : row(tau)$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v_1 matches p_1 : tau_1$,
        $dots.c$,
        $v_n matches p_n : tau_n$,
        $ mat(v_1, dots.c, v_n) matches mat(p_1, dots.c, p_n) : mat(tau_1, dots.c, tau_n) $,
      )),
    ),
  )
]

We also allow a row $row(v)$ to match a matrix $bold(P)$ of the same width with types $row(tau)$ if it matches a row in $bold(P)$

#showybox[
  *$row(v) matches bold(P) : row(tau)$*

  $
    row(v) matches mat(row(p)_1; dots.v; row(p)_m) : row(tau) #h(.5cm) <==> #h(.5cm) exists j | row(v) matches row(p)_j : row(tau)
  $
]

== Semantics of pattern-matching and operations

#let sem(p, t) = $[|#p|]_#t$

*Definition (patterns as sets)* For all type row $row(tau)$ and pattern matrix $bold(P)$, we define $ sem(bold(P), row(tau)) := {row(v) | row(v) matches bold(P) : row(tau) } $ the set of value rows matching the matrix $bold(P)$ and whose components have types $row(tau)$.

*Observations* From this general definition we obtain some simple identities :
- if $bold(P) = mat(row(p)_1; dots.v; row(p)_m)$ then we can decompose the set of values matched by $bold(P)$ like so : $ sem(bold(P), row(tau)) = sem(row(p)_1, row(tau)) union space dots.c space union sem(row(p)_m, row(tau)) $ i.e. the set of values matches by a matrix is simply a disjunction of the sets of values matched by its rows;
- in the same spirit, if $row(p) = mat(p_1, dots.c, p_n)$ and $row(tau) = mat(tau_1, dots.c, tau_n)$, then we have $ sem(row(p), row(tau)) = sem(p_1, tau_1) times space dots.c space times sem(p_n, tau_n) $ i.e. the set of values matches by a row is the cartesian product of the sets of values matched by its components;
- For singleton patterns and types, we have
$
        sem(omega, tau) & = V(tau) \
    sem(not omega, tau) & = diameter \
   sem(p_1 or p_2, tau) & = sem(p_1, tau) union sem(p_2, tau) \
  sem(p_1 and p_2, tau) & = sem(p_1, tau) inter sem(p_2, tau) \
        sem(not p, tau) & = sem(omega, tau) - sem(p, tau)
$
- Finally if we see a value $v$ as a pattern on its own, and if $v: tau$, then $sem(v, tau) & = {v}$.

The interpretation of patterns as sets of values induces an inclusion relation $<=_tau$ on patterns : $ p <=_tau q space <==> space sem(p, tau) subset.eq sem(q, tau) $
This relation is reflexive and symmetric, which makes it a preorder. However the antisymmetry property is not verified in general, since $p <=_tau not not p <=_tau p$ but $p != not not p$.

*Decomposition lemma*
The set of values of type $tau$ can be decomposed as a distinct sum (i.e. a partition) over all constructors $C$ in the signature of $tau$.
$ sem(omega, tau) = union.big.sq_(A^((n)) in "sig" tau) sem(A(omegas(n)), tau) $

The operation $sem(A(omega, ..., omega), tau)$ of restraining the values of type $tau$ to those whose head constructor is $A$ looks promising in order to analyse pattern-matching exhaustivity. However, having to decompose the set of _all_ values of type $tau$ won't be a common task. We would like to decompose the space of values matched by any pattern $p$. Taking the formula above, it is easily achieved by intersecting both sides by $sem(p, tau)$ and simplifying :
$ tau(p) = union.big.sq_(A in "sig" tau) tau(A(omega, ..., omega) and p) $

This is slightly more promising but can be improved further.

Algorithmically, prepending "$A(omega, ..., omega) and$" to $p$ is not very interesting nor useful. Since we are iterating over every constructor $(A "of" row(alpha)) in "sig" tau$, we could instead attempt to define an operation mapping a pattern $p$ to a row $row(r) = r_1, ..., r_n$ such that $ A(row(v)) matches p : tau space <==> space row(v) matches row(r) : row(alpha) $

Intuitively we would like to "unwrap" the constructor $A$ wherever it may appear in $p$.

If $p = A(r_1, ..., r_n)$ this is easy enough as we just need to take the inner $r_i$'s, but it is less clear how to do the same for an or-pattern like $A mat(0, dots.c, 0) or A mat(1, dots.c, 1)$ : we cannot naively "distribute" the disjunction inside $A$ because $sem(A mat(0, dots.c, 0) or A mat(1, dots.c, 1), tau) != sem(A mat(0 or 1, dots.c, 0 or 1), tau)$. The first one matches only two vertices of the unit hypercube, while the second matches all of them.

To solve this problem, we need to map the pattern $p$ to a matrix of all the possible cases the arguments of the constructor $(A "of" row(alpha))$ can be accepted in $p$ : we call this operation _specialization by $A$_, and yields a matrix of width $n$ (the arity of $A$). It is written $p slash A$, and verifies the property
$
  C(row(v)) matches p : tau space <==> space row(v) matches p slash A : row(alpha)
$

*Definition (specialization)*
Specialization by a constructor $(A "of" alpha(n))$ of arity $n$ is defined by induction on $p$ :
$
  omega slash A &= omegas(n) \
  A(row(r)) slash A &= row(r) \
  B(row(r)) slash A &= diameter #h(1cm) "(no row)" \
  (p_1 or p_2)slash A &= (p_1 slash A) or (p_2 slash A) \
  (p_1 and p_2)slash A &=(p_1 slash A) and (p_2 slash A) \
  not A mat(r_1, dots.c, r_n) slash A & = mat(not r_1, omega, dots.c, omega; omega, not r_2, dots.c, omega; dots.v, dots.v, dots.down, dots.v; omega, omega, dots.c, not r_n) \
  not B(r_1, ..., r_m) slash A & = omegas(n) \
  not (p_1 or p_2) slash A & = (not p_1 slash A) and (not p_2 slash A) \
  not (p_1 and p_2) slash A & = (not p_1 slash A) or (not p_2 slash A) \
  not not p slash A & = p slash A
$

We now have a more practical lemma for partitioning the space of values matched by a pattern $p$ with type $tau$.

*Pattern decomposition lemma* $ sem(p, tau) = union.big.sq_(A in "sig" tau) sem(A(p slash A), tau) $
where $A mat(row(p)_1; dots.v; row(p)_m)$ = $A(row(p)_1) or dots.c or A(row(p)_m)$.

#pagebreak()
== Usefulness and exhaustivity

The _pattern-matching exhaustivity_ problem goes as follows : for a pattern matrix $bold(P)$ and a types $row(tau)$, is it true that $ forall row(v), space row(v) : row(tau) space ==> space row(v) matches bold(P) : row(tau) $
Let us denote this property $cal(E)_(row(tau))(bold(P))$

In order to solve pattern-matching exhaustivity, we answer a more general problem : _pattern usefulness_. For a type row $row(tau)$, a matrix $bold(P)$ and a pattern row $bold(q)$, it is denoted $cal(U)_(row(tau))(bold(P), row(q))$ and asks whether the pattern $q$ is "useful" next to matrix $bold(P)$, i.e. does it catch any value row that did not match $bold(P)$. Formally :
$
  cal(U)_(row(tau))(bold(P), row(q)) := exists row(v) : row(tau) | row(v) matches row(q) : row(tau) "and" row(v) mismatches bold(P) : row(tau)
$

This property can be reformulated using pattern-matching semantics :
$ cal(U)_(row(tau))(bold(P), row(q)) space <==> space sem(row(q), row(tau)) - sem(bold(P), row(tau)) != diameter $

Pattern-matching exhaustivity is now a special case of usefulness : $bold(P)$ is exhaustive iff $omegas(n)$ is useless.
$
  cal(E)_(row(tau))(bold(P)) space & <==> space not cal(U)_(row(tau))(bold(P), omegas(n)) \
                                   & <==> space sem(bold(P), row(tau)) = V(row(tau))
$

Pattern usefulness is also useful #emoji.face.tongue in a typechecker when we analyse a #raw("match", lang: "ocaml") expression and want to find redundant clauses : we simply ask whether a clause is useful with respect to the matrix that precedes it. If not then it is redundant.
