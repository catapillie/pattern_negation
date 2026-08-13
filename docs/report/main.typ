#import "template.typ": report
#import "@preview/showybox:2.0.4": showybox
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/xarrow:0.4.0": *
#import "@preview/cetz:0.5.2"

#show: report.with(
  title: [Adding pattern negation to ML-like matching],
  student: "---",
  supervisor: "---",
  date: "05/01/26 - 07/13/26",
  dep: "Département d'informatique",
)

#show raw: set text(font: "JetBrains Maple Mono")
#show link: set text(blue)

#let ocaml = smallcaps("OCaml")
#let rocq = smallcaps("Rocq")
#let ml(code) = $#raw(code, lang: "ocaml")$

= Introduction

== Context

Modern programming languages have evolved to show an increasing number of functional features in order to eliminate bugs and unsound programs before they are executed. It is not uncommon nowadays, when choosing a language in which to develop, to check whether said language features _static typing_ at compile-time to ensure no values of different _types_ are used in an undefined manner. Most functional languages will allow programmers to define their own types, generally in the form of _inductive definitions_, which can be seen as a disjoint sum of tagged values. We choose #ocaml @leroy:hal-00930213 as the language of study for this internship. For example, it lets us define the type of lists of integers as a naturally recursive data structure, like follows :
#align(center)[```ocaml type intlist = Nil | Cons of int * intlist```]
Following this example, the empty list would be #ml("Nil"), and the list [1, 2, 3] would be #ml("Cons (1, Cons (2, Cons(3, Nil)))"), the two previous values being of type #ml("intlist"). With such type definitions, it is very natural for functional languages to provide a syntax to "deconstruct", or "unwrap" their inner values. For instance, if we desired to calculate the length of a list of type #ml("intlist"), we could use the following recursive definition :
#align(center)[
  ```ocaml
  let rec length l =
    match l with
    | Nil          -> 0
    | Cons (x, xs) -> 1 + length xs
  ```
]

In this #ocaml code snippet, we use the _pattern matching_ syntax #ml("match z with") to deconstruct a _scrutinee_ value #ml("z") according to a list of patterns, each binding the inner values of #ml("z") and mapping them to a new expression, which is then evaluated if #ml("z") so happened to look like the pattern in that branch.

Type-checking such a pattern-matching expression ensures that every branch accepts values of the same type, and that they each map to an expression of the same type. Hence, pattern-matching operates on a single type as a way to decompose the set of values of that type. The natural question to then ask is : does a pattern-matching expression handle every possible case for the type being matched over? Ideally, a good compiler ought to warn programmers about a _partial pattern-matching_, as an unhandled case would likely raise an exception of some sort (#ml("Match_failure") in #ocaml), potentially unintended by the programmer, despite usually being very well-defined (and sometimes useful) behavior. Modern type systems like Hindley-Milner do not a priori extend type-checking to answer a predicate like "is this pattern-matching exhaustive?", so this step on its own requires a dedicated analysis.

== Objectives

The main objective of this internship is to extend pattern-matching as seen in #ocaml with pattern negation : values matching a pattern #ml("not(p)") are exactly those who do not match the pattern #ml("p"). While such patterns are never truly necessary in #ocaml, they have the potential to allow for clearer code. Indeed, they allow to explicitly handle "unwanted" cases first in a defensive clause, then treat the rest as usual, as opposed to having a fallback clause laying at the end of the #ml("match") expression. Moreover, if we have a non-exhaustive #ml("match") expression, its negation describes the space of values unmatched by the expression. The following snippet is a simplified example found in real life code from the #ocaml compiler.
#align(center)[
  ```ocaml
  match typ with
  | Tpoly (ty, []) -> instance env ty
  | Tpoly (ty, tl) -> snd (instance_poly false tl ty)
  | Tvar _ ->
      let ty' = newvar () in
      unify env (instance_def typ) (newty (Tpoly (ty', [])));
      ty'
  | _ -> assert false
  ```
]

Using pattern negation, we can handle the degenerate case first. The result expression conveys our intentions better, as we are directly able to read what the forbidden values are.
#align(center)[
  ```ocaml
  match typ with
  | not (Tpoly _ | Tvar _) -> assert false
  | Tpoly (ty, []) -> instance env ty
  | Tpoly (ty, tl) -> snd (instance_poly false tl ty)
  | Tvar _ ->
      let ty' = newvar () in
      unify env (instance_def typ) (newty (Tpoly (ty', [])));
      ty'
  ```
]

Pattern negation is also a current feature wish on the official #ocaml GitHub repository. In this internship we looked at how well this feature could be implemented in the language, with minimal impact on the preexisting code and performance of the compiler.

== Approach

Our approach for the internship was to rely on the existing literature on pattern-matching analysis and compilation and to try to give a natural extension to pattern negation. We also decided to study "and"-patterns, as we realized their description came essentially for free. The algorithm and procedures described in this report were also implemented for a minimal toy language to experiment with different implementation details. Even if we do not aim to describe compilation here, an effort was made to implement it anyway as a starting point for a more efficient algorithm.

During the internship, we figured it would be relevant to formalize some details in the #rocq proof assistant. This turned out to be very useful when checking lemmas by hand became too mechanical, and sometimes helped us understand what didn't work in different attempts to study the problem.

All practical work done during the internship can be found on the public repository #link("https://github.com/catapillie/pattern_negation")

= Pattern-matching in a minimal language

A great number of elements described in the rest of the report heavily rely on the existing literature of pattern-matching analysis and compilation. We explicitly draw the line between the use of said references and our original work.

== Syntax

#let sig = $"sig"$
#let empty = $emptyset$

The problem of pattern-matching exhaustivity was already defined and studied in _Warnings for pattern matching_ @MARANGET_2007 in a publication which now serves as a canonical reference for pattern-matching analysis and compilation in the #ocaml compiler.

We will work with a minimal abstract language consisting of _values_, _patterns_ and _types_. We do not describe what the types look like, but we assume to be able to retrieve their definitions as if they were introduced by an inductive data structure definition. Hence we first introduce an infinite set of constructors ${A, B, C_1, C_2, ...}$, which all have a fixed arity. Then we introduce the set of types $cal(T)$, and for any type $tau$ we claim to know what its _signature_ is : a signature is a set of constructors each equipped with as many type argument as their arity. The signature of a type $tau$ is written $sig(tau)$. For a constructor $C$ of arity $k$ and types $tau_1, ..., tau_k$, we can write $(C "of" tau_1, dots.c, tau_k) in sig(tau)$ to designate the type arguments of $C$ in the signature of $tau$, and sometimes omit the type arguments when we only care to know whether $C in sig(tau)$, or $C$ is of arity 0. Some common types in #ocaml would thus be modeled as :
$
  sig(ml("intlist")) & := {(ml("Nil")), (ml("Cons") "of" ml("int"), ml("intlist"))} \
      sig(ml("int")) & := {dots.c, ml("-1"), ml("0"), ml("1"), dots.c} approx ZZ \
   sig(ml("string")) & := {ml("\"\""), ml("\"a\""), ml("\"b\""), dots.c, ml("\"aa\""), ml("\"ab\""), dots.c} \
    sig(ml("empty")) & := empty #h(.5cm) "(the empty type)"
$

Notice in the above examples how a signature might be infinite or sometimes empty. This presents a challenge when analyzing exhaustivity, because somehow we need to detect whether an infinite amount of values will always be handled by a pattern-matching expression, or conversely, when a pattern-matching is _useless_ for the type being matched over is empty.

Next, _pattern_ and _values_ are defined as follows, the base case being values with no arguments in both definitions.

$
  #text[*pattern*] p & := omega                       &      #h(1cm) "wildcard" \
                     & #h(.5em) | C(p_1, dots.c, p_k) & #h(2cm) "constructor" C \
                     & #h(.5em) | p or q              &   #h(2cm) "disjunction" \
                     & #h(.5em) | p and q             &   #h(2cm) "conjunction" \
                     & #h(.5em) | not p               &      #h(2cm) "negation" \
                     \
    #text[*value*] v & := C(v_1, dots.c, v_k)         & #h(2cm) "constructor" C \
$

In a proper formal description for a programming language, we would except patterns to also contain a way to talk about variable patterns, so as to be able to bind values when a value matches a pattern, like #ml("Cons (_, xs)"). While they are an essential element within the context of compilation, they are totally irrelevant when it comes to pattern-matching exhaustivity analysis, so we may assume every pattern has been stripped of its variables.

#let row(x) = $arrow(#x)$
#let unit = $mat()$
#let omegas(n) = $row(omega)^#n$
#let empty = $diameter$

The general idea to analyze pattern-matching is to consider a whole pattern-matching expression "at once" as a matrix of patterns. Indeed, we need at some point to unwrap a pattern $C(p_1, ..., p_n)$ to its arguments $p_1, ..., p_n$ and we need need to matches $n$ values $v_1, ..., v_n$ to the $p_i$'s all at once. In order to do so, we introduce more generally _rows of values_, _patterns_ and _types_, which will be denoted with an arrow :
$ row(tau) = mat(t_1, dots.c, t_n) #h(1cm) row(p) = mat(p_1, dots.c, p_n) #h(1cm) row(v) = mat(v_1, dots.c, v_n) $

Note that rows are allowed to be empty, and we will write them as unit rows : $unit$. We also see singleton rows $row(tau) = mat(tau_1)$ simply as the inner type $tau_1$, so that we are able to give general definitions over patterns and rows simultaneously. A constructor pattern $A(p_1, ..., p_n)$ can thus be rewritten as $A(row(p))$, and so on. We will also write $omegas(n) = (omega, ..., omega)$ the row with $n$ wildcard patterns. In addition, we consider _matrices of patterns_, appearing with different notations.
$
  bold(P) = mat(p_(1 1), dots.c, p_(1 n); dots.v, dots.down, dots.v; p_(m 1), dots.c, p_(m n)) = mat(row(p)_1; dots.v; row(p)_m)
$
Pattern matrices of height 1 can be seen as singles rows on their own. The _empty matrix_, i.e. the matrix with no rows, is written $empty$. Matrices are a natural object to consider when compared to the usual syntax for pattern-matching expressions on multiple values at once. Each row (or "clause") in a matrix matches a specific set of values, and taking the union of these sets gives us the set of values matched by the whole matrix. We are now able to translate pattern-matching expressions in #ocaml to matrices like so :

#align(center)[
  #columns(3)[
    ```ocaml
    match x, y with
    | Some _, _
    | _, Some _
    | None, None
    ```
    #colbreak()
    #v(.6cm)
    $xarrow(#h(10em))$
    #colbreak()
    $
      mat(
        #raw("Some") omega, , omega;
        omega, , #raw("Some") omega;
        #raw("None"), , #raw("None")
      )
    $
  ]
]

== Typing

To simplify things a little with no loss of generality, we disallow the same constructor to appear twice in $sig(tau)$ with different type arguments. This assumption is entirely justified for if we have $(A "of" tau_A)$ and $(A "of" tau_B)$ both in $sig(tau)$, then we can rewrite the second $A$ as a fresh constructor $B in.not sig(tau)$.

*Definition* A value $v$ is of type $tau$, written $v:tau$, according the following rule. The relation is naturally extended to rows of values and types.

#showybox[
  *$v : tau$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v_1 : tau_1$,
        $dots.c$,
        $v_n : tau_n$,
        $(A "of" tau_1, dots.c, tau_n) in sig(tau)$,
        $A(v_1, ..., v_n) : tau$,
      )),
    ),
  )

  *$row(v) : row(tau)$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v_1 : tau_1$,
        $dots.c$,
        $v_n : tau_n$,
        $ mat(v_1, dots.c, v_n) : mat(tau_1, dots.c, tau_n) $,
      )),
    ),
  )
]

It is important to note that in #ocaml, the only way that typing intervenes in pattern-matching analysis is when we need to extract a full signature from a type. Other than this, @MARANGET_2007 makes the assumption that every pattern has at least one matching value, despite the contradictory existence of the empty type (#ml("type empty ;;")) which is explicitly ignored. We make an effort to bring back typing as part of pattern-matching semantics so that we are able to detect whenever a pattern-matching expression is trivially exhaustive.

#pagebreak()
== Semantics

#let matches = $in$
#let mismatches = $in.not$

We now consider _typed pattern-matching_ as a relation between values, patterns and types. It is then extend to allow value-rows to match a pattern matrix with a type-row. A value _$v$ matches $p$ with type $tau$_, written $v matches p : tau$, whenever we can derive such a judgment from the following rules :

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
        $row(v) matches row(p) : row(tau_i)$,
        $(A "of" row(tau_i)) in sig(tau)$,
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
        $v matches p_1 and p_2 : tau$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $exists i, v_i matches not p_i : tau_i$,
        $v_1 : tau_1$,
        $dots.c$,
        $v_n : tau_n$,
        $(A "of" tau_1, dots.c, tau_n) in sig(tau)$,
        $A(v_1, ..., v_n) matches not A(p_1, ..., p_n) : tau$,
      )),
      prooftree(rule(
        $A != B$,
        $v_1 : tau_1$,
        $dots.c$,
        $v_n : tau_n$,
        $A, (B "of" tau_1, dots.c, tau_n) in sig(tau)$,
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

  *$row(v) matches bold(P) : row(tau)$*

  $
    mat(v_1, dots.c, v_n) matches mat(p^((1))_1, dots.c, p^((1))_n; dots.v, dots.down, dots.v; p^((m))_1, dots.c, p^((m))_n) : mat(tau_1, dots.c, tau_n) #h(.5cm) <==> #h(.5cm) exists j | forall i, space v_i matches p^((j))_i : tau_i
  $
]

Again, if we restrict our language of patterns to variables, constructors and "or"-patterns, the definition is pretty much identical to the way it is presented in @MARANGET_2007, except that we consider both pattern-matching _and_ typing at the same time. This change may seem of little use at first, but it unlocks a useful way to talk about types and patterns with respect to pattern-matching analysis.

On the surface, extending this definition to "not"-patterns may seem simple enough given the very short intuitive definition. Yet, one quickly runs into all kinds of issues when trying to rigorously. Since we are defining the typed pattern-matching relation by induction, we cannot introduce a rule where the premise is negated. Our choice was to keep a single relation, and whenever we need to proove a judgment of the form $v matches not p : tau$, we destruct on $p$ again. Notice that when we have a non-trivial negation like $not (p or q)$ or $not (p and q)$, we essentially apply De Morgan's rules to define the pattern-matching relation.

Pattern negation also introduces more difficulty with regards to exhaustivity analysis, as the programmer is now able to express _impossible_ patterns (those who match no values). Some obvious examples would be $not omega$ (negation of everything), or the conjunction of two different constructors like $ml("None") and ml("Some")$. Ideally, we would like the #ocaml compiler to warn us about these kind of patterns, with a message of the form "this pattern matches no values!". Finally, if we introduced back binding patterns into our language, one would realize variables cannot be bound if nested inside a #ml("not").

#let sem(p, t) = $[|#p|]_#t$

*Definition* For all type row $row(tau)$ and pattern matrix $bold(P)$, we define the set of value rows matching the matrix $bold(P)$ and whose components have types $row(tau)$ by $ sem(bold(P), row(tau)) := {row(v) | row(v) matches bold(P) : row(tau) } $

This interpretation of patterns allows us to talk about patterns like sets of values, and operations between patterns are naturally translated to their corresponding set operation. In fact, these are essentially obvious from simple identities :
- if $bold(P) = mat(row(p)_1; dots.v; row(p)_m)$ then we can decompose the set of values matched by $bold(P)$ like so : $ sem(bold(P), row(tau)) = sem(row(p)_1, row(tau)) union space dots.c space union sem(row(p)_m, row(tau)) $ i.e. the set of values matches by a matrix is simply a disjunction of the sets of values matched by its rows;
- in the same spirit, if $row(p) = mat(p_1, dots.c, p_n)$ and $row(tau) = mat(tau_1, dots.c, tau_n)$, then we have $ sem(row(p), row(tau)) = sem(p_1, tau_1) times space dots.c space times sem(p_n, tau_n) $ i.e. the set of values matches by a row is the cartesian product of the sets of values matched by its components;
- $sem(omegas(n), row(tau))$ is the set of value-rows with types $row(tau)$, and it includes $sem(row(p), row(tau))$ for any row $row(p)$. Indeed, we have $row(v) matches bold(P) : row(tau) ==> row(v) : row(tau)$ for all rows $row(v), row(tau)$ and matrices $bold(P)$.
- For singleton patterns and types, we have
$
    sem(not omega, tau) & = diameter \
   sem(p_1 or p_2, tau) & = sem(p_1, tau) union sem(p_2, tau) \
  sem(p_1 and p_2, tau) & = sem(p_1, tau) inter sem(p_2, tau) \
        sem(not p, tau) & = sem(omega, tau) \\ sem(p, tau)
$

Moreover, we find that this formalization of pattern-matching exhibits some properties similar to those of classical logic :
- law of the excluded middle : $forall (v, p, tau), space (v matches p : tau) "or" "not" (v matches p : tau)$
- double negation : $forall (v, p, tau), space v matches p : tau space <==> space v matches not not p : tau$

At some point during the internship, these lemmas were formalized in the #rocq proof assistant to ensure the correctness of our definitions. We chose to represent sets of values using the `Stdlib.Sets.Ensembles` module, which models sets as predicates over the type of the elements.

== Decomposition and matrix specilization

The most common way to analyse exhaustivity in the literature is by "dividing" a pattern matrix into different submatrices, one for each constructor in the signature of a type $tau$. Consider the #ocaml type definition #raw("type") $tau_1$ #raw("= A of") $tau_11$ #raw("| B ") and the following pattern-matching problem :
$ bold(P) = mat(A(p_1), q_1; A(p_2), q_2; B, q_3) $
Because the signature of #ml("t") is ${A, B}$, we can partition the space of values $sem(bold(P), tau_1\, tau_2)$ with two disjoint subsets $P_A, P_B$ of value-rows starting with $A(dots.c)$ and $B$ respectively. Looking at $bold(P)$, we also notice how the two first row would only match values in $P_A$, whereas the last would only match those in $P_B$. Hence, if we somehow knew if the two following matrices "$bold(P)slash A$" and "$bold(P)slash B$" were exhaustive
$ bold(P) slash A = mat(p_1, q_1; p_2, q_2) #h(1cm) bold(P) slash B = mat(q_3) $
... then surely $bold(P)$ is exhaustive as well since we would have treated every constructor in $sig(tau_1)$. A naive way to express such a partition of a pattern $p$ is to conjunct it with a pattern that matches every value starting with a constructor $A$ :

$
  sem(p, tau) = union.sq.big_(A in sig(tau)) (sem(p, tau) inter sem(A(row(omega)), tau)) = union.sq.big_(A in sig(tau)) sem(p and A(row(omega)), tau)
$

Algorithmically, appending "$and A(row(omega))$" to $p$ is not very interesting nor useful. Since we are iterating over every constructor $(A "of" row(tau_(1 i))) in sig(tau_1)$, we could instead attempt to define a more general operation mapping a matrix $bold(P)$ to a new matrix $bold(P) slash A$ such that :
$
  mat(A(row(v_(1 i))), v_2, dots.c, v_n) matches bold(P) : mat(tau_1, dots.c, tau_n) space <==> space mat(row(v_(1 i)), v_2, dots.c, v_n) matches bold(P) slash A : mat(row(tau_(1 i)), tau_2, dots.c, tau_n)
$

This operation on matrices is called _specialization by $A$_, as seen in @MARANGET_2007, which described it by mapping each row to a new matrix, then flattening the result vertically as a new matrix. In order to define it ourselves with pattern negation, we first need to introduce some utility operations between matrices :
- $bold(P) or bold(Q)$ stacks two matrices of the same with vertically. The choice of notation is coherent with the intuition that a value matching $bold(P) or bold(Q)$ will match at one of them.
- $bold(P) and bold(Q)$, is similarly the matrix whose matching value rows are those of $bold(P)$ _and_ $bold(Q)$ simultaneously (again, these are of same width). We compute it by taking a cartesian product of the rows, then taking the conjunction of every pair of rows. The definition is illustrated by the example:
  $mat(1, 2; 3, 4) and mat(5, 6; 7, 8) = mat(1 and 5, 2 and 6; 3 and 5, 4 and 6; 1 and 7, 2 and 8; 3 and 7, 4 and 8)$.

At last, here is our definition.

*Definition (specialization)*
Specialization by a constructor $(A "of" row(tau_i))$ of arity $n$ is defined by induction on $p$ :
#columns(2)[
  #v(1cm)
  $
           omega slash A & = omegas(n) \
       A(row(r)) slash A & = row(r) \
       B(row(r)) slash A & = diameter #h(1cm) "(no rows)" \
     (p_1 or p_2)slash A & = (p_1 slash A) or (p_2 slash A) \
    (p_1 and p_2)slash A & =(p_1 slash A) and (p_2 slash A) \
  $
  #colbreak()
  $
    not omega slash A & = empty #h(1cm) "(no rows)"\
    not A mat(r_1, dots.c, r_n) slash A & = mat(not r_1, omega, dots.c, omega; omega, not r_2, dots.c, omega; dots.v, dots.v, dots.down, dots.v; omega, omega, dots.c, not r_n) \
    not B(r_1, ..., r_m) slash A & = omegas(n) \
    not (p_1 or p_2) slash A & = (not p_1 slash A) and (not p_2 slash A) \
    not (p_1 and p_2) slash A & = (not p_1 slash A) or (not p_2 slash A) \
    not not p slash A & = p slash A
  $
]
Specilization of a matrix is done by specializing each pattern in the column and stacking the resulting matrices vertically (in the sense of $or$). If $bold(P)$ is of width $n$ and $A$ of arity $k$, then $bold(P) slash A$ will be of width $k+n-1$.
$
  mat(p_1, row(p)'_1; dots.v, dots.v; p_m, row(p)'_m) slash A = mat((p_1 slash A), row(p)'_1; dots.v, dots.v; (p_m slash A), row(p)'_m)
$

For example, with a constructor #ml("Pair"):
$mat(
  #ml("Pair")\(1\, 2\), 3;
  not#ml("Pair")\(1\, 2\), 4;
  B(2), omega
) slash #raw("Pair") = mat(1, 2, 3; not 1, omega, 4; omega, not 2, 4)$.

We can also define how to specialize a type row $mat(tau_1, dots.c, tau_n)$ by a constructor $(A "of" row(tau_(1 i)))$ of arity $k$, the first component is simply expanded to the types $tau_(1 1), dots.c, tau_(1k)$.

*Lemma* This definition of specialization satisfies the desired property : $ row(v) matches bold(P) : row(tau) <==> row(v)slash A matches bold(P)slash A : row(tau)slash A $

Finally, for convenience, we define a "reciprocal" operation which takes a matrix $bold(P)$ of with at least $k$ and simply consumes the first $k$ columns, which we simply note $A(bold(P))$ since it generalizes constructor patterns $A(row(p))$. If $row(p)_1, ..., row(p)_m$ are of width $k$, then
$
  A mat(row(p)_1, row(p)'_1; dots.v, dots.v; row(p)_m, row(p)'_m) = mat(A(row(p)_1), row(p)'_1; dots.v, dots.v; A(row(p)_m), row(p)'_m)
$

Now, we obtain a more expressive decomposition lemma to partition the set of values matched by a matrix.

*Theorem (signature decomposition)*
$ sem(bold(P), row(tau)) = union.big.sq_(A in "sig" tau_1) sem(A(bold(P) slash A), row(tau)) $

= Exhaustivity analysis

== Formal description

The _pattern-matching exhaustivity_ problem goes as follows : for a pattern matrix $bold(P)$ and a types $row(tau)$, do we have the following property? $ forall row(v), space row(v) : row(tau) space ==> space row(v) matches bold(P) : row(tau) $
Let us denote this property $cal(E)_(row(tau))(bold(P))$

In order to solve pattern-matching exhaustivity, we answer a more general problem : _pattern usefulness_. For a type row $row(tau)$, and two matrices $bold(P)$ and $bold(Q)$, it is denoted $cal(U)_(row(tau))(bold(P), bold(Q))$ and asks whether the matrix $bold(Q)$ is "useful" next to $bold(P)$, i.e. if it catches any value row that do not match $bold(P)$. Formally :
$
  cal(U)_(row(tau))(bold(P), bold(Q)) := exists row(v) : row(tau) | row(v) matches bold(Q) : row(tau) "and" row(v) mismatches bold(P) : row(tau)
$

which can be restated as :
$cal(U)_(row(tau))(bold(P), bold(Q)) <==> sem(bold(Q), row(tau)) \\ sem(bold(P), row(tau)) != empty$.

Pattern-matching exhaustivity is now a special case of usefulness : $bold(P)$ is exhaustive iff $omegas(n)$ is useless with respect to $bold(P)$.
$
  cal(E)_(row(tau))(bold(P)) space & <==> space not cal(U)_(row(tau))(bold(P), omegas(n)) \
                                   & <==> space sem(bold(P), row(tau)) = sem(omegas(n), row(tau))
$

These two defintions come directly from @MARANGET_2007 (adapted to our notations), except with a major distiction : in our version, $bold(Q)$ is a matrix, where is used to be a single row $row(q)$ in the original article. We chose to introduce matrices directly as we believed they would directly translate to a more efficient algorithm. That being said, the original paper does explore a different way to compute this property with a more optimized approach we won't be going over in this report.

Pattern usefulness comes as a convenient generalization when we need to check whether a clause in a #ml("match") expression is redundant : we simply ask said clause is useful with respect to the matrix that precedes it : if not then it is redundant.

== Computing the solution

Thanks to our decomposition lemmas, we can derive an algorithm to determine whether $cal(U)_(row(tau))(bold(P), bold(Q))$ is true. We work throughout this section with a type row $row(tau) = mat(tau_1, dots.c, tau_n)$.

- There are two "easy" base cases :
  - if $bold(P) = empty$ (no rows), then no value is forbidden, and we need to ensure that there exists a row in $bold(Q)$ that matches at least one value. In short, we say
  $ cal(U)_(row(tau))(empty, bold(Q)) <==> sem(bold(Q), row(tau)) != empty $

  - if $bold(P)$ and $bold(Q)$ are of width zero (they are unit matrices) and $bold(P) != empty$, then $sem(bold(P), unit) = sem(omegas(0), unit)$, thus $bold(P)$ is exhaustive and $bold(Q)$ can match no more (unit) values. Hence : $ cal(U)_(row(tau))(unit, unit) <==> bot $

  - In any other case, we need to apply the decomposition lemma on what we think the pattern matrix $bold(Q) \\ bold(P)$ is. If $S(bold(P)) union S(bold(Q))$ is a complete signature, then the set of matched values is decomposed like so :
    $
      sem(bold(Q), row(tau)) \\ sem(bold(P), row(tau)) &= (union.sq.big_(A in S(bold(P)) union S(bold(Q))) sem(A(bold(Q) slash A), row(tau))) \\ sem(bold(P), row(tau)) \
      &= union.sq.big_(A in S(bold(P)) union S(bold(Q))) sem(A(bold(Q) slash A), row(tau)) \\ sem(A(bold(P) slash A), row(tau))
    $

    hence usefulness is rewritten as :
    $
      cal(U)_row(tau)(bold(P), bold(Q)) <==> or.big_(A in S(bold(P)) union S(bold(Q))) cal(U)_(row(tau) slash A)(bold(P) slash A, bold(Q) slash A)
    $

    Otherwise, we need one extra term taking into account constructors that do not appear in $bold(P)$ or $bold(Q)$. It can be obtained by simply removing the first column, but it can also be thought of specializing by a fresh constructor of arity 0. For this reason, we introduce the notation $bold(P) slash omega$ to do exactly this, hence :

  // which gives
  $
    cal(U)_row(tau)(bold(P), bold(Q)) <==> or.big_(A in S(bold(P)) union S(bold(Q))) cal(U)_(row(tau) slash A)(bold(P) slash A, bold(Q) slash A) #h(1em) or #h(1em) cal(U)_(row(tau) slash omega)(bold(P) slash omega, bold(Q) slash omega)
  $

== Eliminating useless recursive calls

At this point, we have a recursive algorithm, but there may be an optimization we can incorporate into this last case, which consists in performing less recursive calls. The idea is to only specialize against constructors which appear in $bold(Q)$ or _strictly negatively_ in $bold(P)$. Indeed, we need not to specialize against those who appear positively, since we already know that the signature is incomplete, and so the usefulness check may yield true anyway when specializing "by $omega$". It is still required however to specialize against strictly negative constructors, since they may omit a value that could still be useful to $bold(P)$. Consider the following matrix $bold(P)$ as an example.
$ bold(P) = mat(1; not 2) $
By definition, we know that $cal(U)_#raw("int") (bold(P), 2)$ is true, since $2$ is unmatched by $P$. Our initial decomposition lemma tells us to perform three recursive calls, specializing by $1$, $2$ and $omega$ respectively :
$
  cal(U)_#raw("int") (bold(P), 2) space <==> space underbrace(cal(U)_unit (unit, empty), slash 1) space or space underbrace(cal(U)_unit (empty, unit), slash 2) space or space underbrace(cal(U)_unit (unit, unit), slash omega)
$
Observe how the result equals $top$ because of the one recursive call specializing by constructor $2$. And if there are no strictly negative constructors, then we have for instance
$
  cal(U)_#raw("int") (mat(1; 2), 3) space <==> space underbrace(cal(U)_unit (empty, unit), slash omega) space <==> space top
$
with no need for other recursive calls, because the signature is incomplete _and_ we are not omitting a constructor in $bold(P)$ (there are no strictly negative constructors), which means we can restrain our search to the default matrix. We did not show the equivalence between usefulness and this smaller sum.

*Conjecture (optimized recursive case with pattern-negation)*
$
  cal(U)_row(tau)(bold(P), bold(Q)) <==> or.big_(A in S(bold(Q)) union (S^-(bold(P)) \\ S^+(bold(Q)))) cal(U)_(row(tau) slash A)(bold(P) slash A, bold(Q) slash A) #h(1em) or #h(1em) cal(U)_(row(tau) slash omega)(bold(P) slash omega, bold(Q) slash omega)
$

The code in our prototype implementation uses this conjecture to check pattern-matching exhaustivity.

= Final remarks

== $sans("NP")$-hardness

As it turns out, checking the exhaustivity property for a pattern-matching is computationally hard, as mentioned by @MARANGET_2007, citing @sekar:apm. This is easily shown by reducing the boolean satisfiability problem to a pattern-matching expression whose unhandled cases are exactly the satisfiability solution. For a SAT boolean formula in conjunctive normal form, we can write a #ml("match") expression which handles every disjunctive clause by matching the negation of each literal. As such, any unhandled case will necessarily satisfy one of the boolean clauses. This is the explanation given by @rustnp in a blog post on the hardness of compiling the #smallcaps[Rust] programming language.

#columns(3)[
  #v(2.5em)
  $ x and y and (x or y) and (not x or not y) $
  #colbreak()
  #v(2.5em)
  #set align(center)
  $xarrow("... formula transformed into ...")$
  #colbreak()
  ```ocaml
  match x, y with
    false, _      -> ()
  | _    , false  -> ()
  | false, false  -> ()
  | true , true   -> ()
  ```
]

The associated #ml("match") expression is  exhaustive, so the formula is not satisfiable. Judging by this result, we can a priori expect our algorithms to exhibit exponential behavior in time complexity.


== In the real world

Towards the end of the internship, after various experiments with a toy implementation, we wanted to try and hack the #ocaml compiler for a minimal working implementation. While we did not succeed entirely, we noticed that the previous optimization work established in @MARANGET_2007 and other papers were hardly compatible with our minimal implementation. We found it difficult to adapt the exisiting code without introducing major changes to the structure of the definitions in the relevant parts. Currently, the #ocaml compiler stratifies patterns by required them to be stripped of their variables, then simplified in the presence of head or-pattern, turning them into "simple" patterns. We did not exactly figure out where not-pattern would lie in this hierarchy, leading us to modify it slightly, which prompted a lot of changes in the codebase.

Speaking of compilation, we have yet to look into how the compilation of not-patterns can be optimized to yield better target code. #ocaml already employs a few tricks here and there to generate as less redundant code as possible, by swapping _incompatible_ rows in a pattern matrix (two rows are incompatible when they cannot match the same values simultaneously). A promising idea may be to consider what happens when we try to rewrite a #ml("match") expression without using not-patterns, in traditional "vanilla" #ocaml :

#columns(3)[
  ```ocaml
  match
    not (1|2) -> "rest"
  | 1 -> "one"
  | 2 -> "two"
  ```
  #colbreak()
  #v(2.5em)
  #set align(center)
  $xarrow("without pattern negation")$
  #colbreak()
  ```ocaml
  match
  | 1 -> "one"
  | 2 -> "two"
  | _ -> "rest"
  ```
]

Not patterns can sometimes by thrown at the bottom of a match when they handle a special "error" case, and under this form, the already optimized #ocaml pattern matching compilation algorithms could take over, if the lowered match expression doesn't grow too large in size.

== A different approach to the problem

Our initial leading idea in the internship was to notice that values as described here are a strict subset of patterns, prompting us to extend the matching relation $v matches p$ to a more general preorder relation $p subset.eq q$ between patterns, defined by :
$ p subset.eq q #h(1em) #text[*iff*] #h(1em) forall v, (v matches p ==> v matches q) $

This relation can intuitively be thought of as $p$ being _included_ in $q$, or $q$ being more _general_ than $p$. As such, the exhaustiveness of a pattern $p$ could thus be obtained by proving something like $omega subset.eq p$, meaning every value matches $p$. Working with such a relation was an interesting idea because it is indeed used in the #ocaml compiler for pattern-matching optimization; see @maranget_lefessant_optim. We attempted to give a syntactic inductive definition for the relation $p subset.eq q$, but it became obvious that it would be too hard. The main issue we ran into was trying to gave inference rules for $p subset.eq q_1 or q_2$ in the special case where we had neither $p subset.eq q_1$ nor $p subset.eq q_2$, as drawn in the following diagram.

#align(center)[
  #cetz.canvas({
    import cetz.draw: *

    let r = 1.75
    let dist = 1.0

    circle(
      (-dist, 0),
      radius: r,
      stroke: 1.5pt + rgb("#2b5c8f"),
      fill: rgb("#2b5c8f35"),
    )

    circle(
      (dist, 0),
      radius: r,
      stroke: 1.5pt + rgb("#d9534f"),
      fill: rgb("#d9534f35"),
    )

    circle(
      (0, 0),
      radius: 1.2,
      stroke: (dash: "dashed", paint: rgb("#2e7d32"), thickness: 1.5pt),
      fill: rgb("#2e7d3245"),
    )

    content((-dist - 0.56, 0.8), text(fill: rgb("#2b5c8f"), weight: "bold", size: 14pt)[*$q_1$*])
    content((+dist + 0.5, 0.8), text(fill: rgb("#d9534f"), weight: "bold", size: 14pt)[*$q_2$*])
    content((0, 0), text(fill: rgb("#1b5e20"), weight: "bold", size: 14pt)[*$p$*])
  })
]

Other quirks were encountered in the presence of pattern negation. Intuitively, the proposition $not p subset.eq q$ should be equivalent to $not q subset.eq p$, because the two patterns $p$ and $q$ are incompatible (they have no matching value in common). In @MARANGET_2007 and @maranget_lefessant_optim, incompatibility is written $p space hash space q$. Adding this relation into the mix, proving basic results in a formal proof assistant such as the transitivity of $subset.eq$ became very hard.

#pagebreak()
= Appendix -- context of the internship

The internship was welcomed within the Picube team of Inria (Institut National de Recherche en Informatique et en Automatique). The team strongly focuses on formal proof assistants and verification, and works in collaboration with IRIF (Institut de Recherche en Informatique Fondamentale), as well as CNRS and the Paris-Cité University.

#columns(4)[
  #v(1cm)
  #image("assets/inr_logo_rouge.png")

  #colbreak()

  #v(0.65cm)
  #image("assets/Logo-irif.png")

  #colbreak()

  #v(1cm)
  #image("assets/UniversiteParisCite_logo_horizontal_couleur_CMJN.jpg")

  #colbreak()

  #v(0.20cm)
  #image("assets/LOGO_CNRS_BLEU.png")
]
