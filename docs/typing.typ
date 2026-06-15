#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/showybox:2.0.4": showybox

#let ocaml = smallcaps([OCaml])

= Typed pattern-matching and pattern negation

We consider $cal(C)_t$ and $cal(C)_v$ two distinct sets, consisting of type constructors and value constructors respectively. All of them have their own arity $k >= 0$.

$
   #text[*type*] tau & := C(tau_1, ..., tau_k)     & #h(2cm) "constructor" C in cal(C)_t \
                     \
  #text[*pattern*] p & := omega                    &                  #h(1cm) "wildcard" \
                     & #h(.5em) | C(p_1, ..., p_k) & #h(2cm) "constructor" C in cal(C)_v \
                     & #h(.5em) | p or q           &               #h(2cm) "disjunction" \
                     & #h(.5em) | p and q          &               #h(2cm) "conjunction" \
                     & #h(.5em) | not p            &                  #h(2cm) "negation" \
                     \
    #text[*value*] v & := C(p_1, ..., p_k)         & #h(2cm) "constructor" C in cal(C)_v \
$

Let's consider a function which maps a type to a _signature_, i.e. a set of value constructors with a finite number of type arguments :
$ "sig" tau = { (C_1 "of" tau_11, ..., tau_(1 n_i)), (C_2 "of" tau_21, ..., tau_(2 n_2)), ... } $

Note that it is allowed
- for types to have an empty signature;
- for value constructors to have no type arguments;
- for signatures to be infinite.

Notice how we ignore that type constructors (in #ocaml for example) are polymorphic : here we only work with specialized types. As such, there is no garantee that types with the same constructor will have similar-looking signatures. For all we know, we could have
$ "sig" (#raw("list") alpha) != "sig" (#raw("list") beta) $

To simply things a little with no loss of generality, we disallow the same constructor to appear twice in $"sig" tau$ with different type arguments. This assumption is entirely justified for if we have $(A "of" alpha)$ and $(A "of" beta)$ both in $"sig" tau$, then we can rewrite the second $A$ as a fresh value constructor $A'$.

*Examples* Common types in #ocaml :
- $"sig" #raw("bool") = { #raw("false"), #raw("true") }$
- $"sig" (#raw("option") alpha) = { #raw("None"), #raw("Some") "of" alpha }$
- $"sig" #raw("empty") = diameter$
- $"sig" #raw("int") = ZZ$

*Definition* A type $tau$ is empty if all of its constructors have at least one empty type argument : $ tau "is empty" space <==> space space forall (C_i "of" tau_1, ..., tau_n) in "sig" tau, exists i | tau_i "is empty" $
This can be seen as an inductive definition.

*Observation* A type whose signature is empty is also empty. Indeed, if $"sig" tau = diameter$ then the statement "$tau$ is empty" is vacuously true.

#let matches = $prec.eq$
We now consider _typed pattern-matching_ as a relation between values, patterns and types. A value _$v$ matches $p$ with type $tau$_, written $v matches p : tau$ if this judgment can be derived from the following rules :

#showybox[
  *$v matches p : tau$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $tau "is not empty"$,
        $v matches omega : tau$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $v_1 matches p_1 : tau_1$,
        $dots.c$,
        $v_n matches p_n : tau_n$,
        $(A "of" tau_1, ..., tau_n) in "sig" tau$,
        $A(v_1, ..., v_n) matches A(p_1, ..., p_n) : tau$,
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

]

*Lemma*  $v matches p : tau <==> v matches not not p : tau$.

*Definition (patterns as sets)* For all type $tau$ and pattern $p$, we define $tau (p) := {v | v matches p : tau }$. If $p = omega$, then we allow the abuse of notation $tau(omega) = tau$, which is intuitively the set of values of type $tau$.

*Observations*
$
    tau(not omega) & = diameter \
   tau(p_1 or p_2) & = tau(p_1) union tau(p_2) \
  tau(p_1 and p_2) & = tau(p_1) inter tau(p_2) \
        tau(not p) & = tau \\ tau(p) \
            tau(v) & = {v}
$

*Lemma* $tau$ is empty iff $tau = diameter$.

*Definition* The value-set interpretation of patterns induces an "inclusion" relation on patterns : $ p <= q space <==> space tau(p) subset.eq tau(q) $
This relation is reflexive and symmetric, which makes it a preorder. However the antisymmetry property is not verified in general, since $p <= not not p <= p$ but $p != not not p$.

*Decomposition lemma*
The set of values of type $tau$ can be decomposed as a distinct sum over all constructors $C$ in the signature of $tau$.
$ tau = union.big.sq_(C in "sig" tau) tau(C(omega, ..., omega)) $

The operation $tau(C(omega, ..., omega))$ of restraining the values of type $tau$ to those whose head constructor is $C$ looks promising in order to analyse pattern-matching exhaustivity. However, having to decompose the set of _all_ values of type $tau$ won't be a common one. We would like to decompose the space of values matched by any pattern $p$. Taking the formula above, it is easily achieved by intersection both sides by $tau(p)$ and simplifying expressions :
$ tau(p) = union.big.sq_(C in "sig" tau) tau(C(omega, ..., omega) and p) $

This is slightly more promising but can be improved further.

Algorithmically, prepending "$C(omega, ..., omega) and$" to $p$ is not very interesting. Since we are iterating over every constructor $(C "of" (tau_1, ..., tau_n)) in "sig" tau$, we could instead attempt to define an operation mapping a pattern $p$ to a list of patterns $r_1, ..., r_n$ such that $ C(v_1, ..., v_n) matches p : tau space <==> space forall i, space v_i matches r_i : tau_i $

Intuitively we would like to "unwrap" the constructor $C$ wherever it may appear in $p$.

If $p = C(r_1, ..., r_n)$ this is easy enough as we just need to take the inner $r_i$'s, but it is less clear how to do the same for an or-pattern like $C(0, ..., 0) or C(1, ..., 1)$ : we cannot naively "distribute" the disjunction inside $C$ because $tau(C(0, ..., 0) or C(1, ..., 1)) != C(0 or 1, ..., 0 or 1)$. The first one matches only two vertices of the unit hypercube, while the second matches all of them. To solve this issue, we will consider _matrices of patterns_ whose rows are of length $n$.

And so, for a value constructor $C$ of arity $n$, we define an operation _specialization by $C$_, written $p slash C$, which maps a pattern $p$ to a pattern matrix of width $n$ $ bold(R) = mat(r^((1))_1, dots.c, r^((1))_n; dots.v, dots.down, dots.v; r^((m))_1, dots.c, r^((m))_n) $ such that
$
  C(v_1, ..., v_n) matches p : tau space & <==> space exists j, forall i, space v_i matches r^((j))_i : tau_i \
                                         & <==> mat(v_1, dots.c, v_n) matches bold(R) : mat(tau_1, dots.c, tau_n)
$

*Definition (specialization)*
Specialization is defined by induction on $p$ :
$
  (dot slash C) : #text[*pattern*] & --> cal(M)(#text[*pattern*]) \
  \
  omega & mapsto.long mat(omega, dots.c, omega) \
  C(r_1, ..., r_n) & mapsto.long mat(r_1, dots.c, r_n) \
  A!=C, #h(.5em) A(r_1, ..., r_m) & mapsto.long diameter \
  p_1 or p_2 & mapsto.long (p_1 slash C) or (p_2 slash C) \
  p_1 and p_2 & mapsto.long (p_1 slash C) and (p_2 slash C) \
  not C(r_1, ..., r_n) & mapsto.long mat(not r_1, omega, dots.c, omega; omega, not r_2, dots.c, omega; dots.v, dots.v, dots.down, dots.v; omega, omega, dots.c, not r_n) \
  A!=C, #h(.5em) not A(r_1, ..., r_m) & mapsto.long mat(omega, dots.c, omega) \
  not (p_1 or p_2) & mapsto.long (not p_1 slash C) and (not p_2 slash C) \
  not (p_1 and p_2) & mapsto.long (not p_1 slash C) or (not p_2 slash C) \
  not not p & mapsto.long (p slash C)
$

We now have a better looking lemma for partitioning the space of values matched by a pattern $p$ with type $tau$.

*Decomposition lemma* $ tau(p) = union.big.sq_(C in "sig" tau) tau(C(p slash C)) $


 