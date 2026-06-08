#let ocaml = smallcaps([OCaml])

#align(center)[
  = Extending pattern-matching in #ocaml with `not` patterns
]

*TODO: context*

== Minimal language

#let matches = $prec.eq$
#let refutes = $prec.eq.not$
#let unitmat = $mat(space; space)$

Let us consider a minimal language of patterns and values with which we will define the semantics of pattern-matching and exhaustivity.

$
  #text[*pattern*] p & := omega                    &        #h(1cm) "wildcard" \
                     & #h(.5em) | C(p_1, ..., p_k) & #h(2cm) "constr." C^((k)) \
                     & #h(.5em) | p or q           &     #h(2cm) "disjunction" \
                     & #h(.5em) | p and q          &     #h(2cm) "conjunction" \
                     & #h(.5em) | not p            &        #h(2cm) "negation" \
    #text[*value*] v & := C(p_1, ..., p_k)         & #h(2cm) "constr." C^((k)) \
$
The base case of values is when we have a constructor of arity 0. In #ocaml, for example, such values are `1`, `2`, `true`, `"abc"`, `None`, and so on.

We assume that every considered constructor $C^((k))$ has a fixed arity $n$, and belongs to a fixed set $cal(K)$. Let us partition the set $cal(K)$ into a set of _signatures_. In #ocaml, we'd have the signature ${#raw("None"), #raw("Some")}$ corresponding to the type `'a option`. Note that signatures may be infinite, such as $NN = {0, 1, 2, ...}$ for the type `int`.

We now define the pattern-matching relation between patterns and values, written $p matches v$. This definition is then immediately extended to rows $arrow(p) = (p_1, ..., p_k)$  and  $arrow(v) = (v_1, ..., v_k)$ :
$
                            omega matches v & #h(1cm)"for any value" v \
  C(p_1, ..., p_k) matches C(v_1, ..., v_k) & #h(1cm) "iff" p_1 matches v_1, ..., p_k matches v_k \
                           p or q matches v & #h(1cm) "iff" p matches v "or" q matches v \
                          p and q matches v & #h(1cm) "iff" p matches v "and" q matches v \
                            not p matches v & #h(1cm) "iff" p refutes v \
                                            \
    (p_1, ..., p_k) matches (v_1, ..., v_k) & #h(1cm) "iff" p_1 matches v_1, ..., p_k matches v_k \
$

It is no longer correct to assume any given pattern $p$ has at least one matching value, like is done in the canonical reference paper for #ocaml pattern-matching @MARANGET_2007. Indeed, the addition of pattern negation has made it possible to write _impossible_ patterns, like $not omega$. Similarly, pattern conjunction allows us to write $#raw("Some") p and #raw("None")$, which won't match any value since the two constructors are distinct. If a pattern $p$ is impossible, we write $p refutes$.

A pattern matrix is a matrix $ bold(P) = mat(p^1_1, dots.c, p^1_m; dots.v, dots.down, dots.v; p^n_1, dots.c, p^n_m) $
with $n$ rows of length $m$. Any matrix with no rows will be written $diameter$. Matrices with one or more rows of size $m=0$ can be written as a unit matrix $mat()$.

A value row $arrow(v)$ can match a matrix $bold(P)$ if and only if $bold(P)$ has a row $arrow(p)$ such that $arrow(p) matches arrow(v)$.

== Operations on rows and matrices

First, we denote $plus.o$ the action of stacking matrices of same width vertically : $ mat(arrow(p_1); dots.v) plus.o mat(arrow(q_1); dots.v) := mat(arrow(p_1); dots.v; arrow(q_1); dots.v) $

We adopt the notation $times.o$ for a special kind of matrix product which performs a cartesian product of the matrices' rows, and combines each pair of row into a row of conjunction patterns. For example :
$
  mat(p_11, p_12; p_21, p_22) times.o mat(q_11, q_12; q_21, q_22; q_31, p_32) := mat(
    p_11 and q_11, p_12 and q_12;
    p_21 and q_11, p_22 and q_12;
    p_11 and q_21, p_12 and q_22;
    p_21 and q_21, p_22 and q_22;
    p_11 and q_31, p_12 and q_32;
    p_21 and q_31, p_22 and q_32;
  )
$

For any signature $Sigma$ and $A^((k)) in Sigma$ of arity $k$, we want to be able to "unwrap" the head constructor by mapping a value $C(v_1, ..., v_k)$ to the row $(v_1, ..., v_k)$. In this spirit, we define an operation that maps a pattern $p$ to a matrix $p slash A$, in which the constructor $A$ in $p$ has been unwrapped. We call this operation _specialization by A_, and is defined by induction on $p$ as follows :
#columns(2, [
  $
               omega slash A & := underbrace((omega, ..., omega), k) \
    A(p_1, ..., p_k) slash A & := (p_1, ..., p_k) \
              B(...) slash A & := diameter \
            (p or q) slash A & := p slash A plus.o q slash A \
           (p and q) slash A & := p slash A times.o q slash A \
  $
  #colbreak()
  $
    not omega slash A & := diameter \
    not A(p_1, ..., p_k) slash A & := underbrace(mat(not p_1, omega, dots.c, omega; omega, not p_2, dots.c, omega; dots.v, dots.v, dots.down, dots.v; omega, omega, dots.c, not p_k), k) \
    not B(...) slash A & := underbrace((omega, ..., omega), k) \
    not (p or q) slash A & := (not p and not q) slash A \
    not (p and q) slash A & := (not p or not q) slash A \
  $
])

Notice how the last two cases are handled by using De Morgan's laws.

Specialization on a nonempty row $(p_1, ..., p_m)$ is done by specializing $p_1$, then concatening $(p_2, ..., p_m)$ to each row in the resulting matrix. Similarly, specializing a matrix $bold(P)$ is done by specializing each row, then stacking the resulting matrices vertically (i.e. in the sense of $plus.o$).

Generally, specializing a matrix $bold(P)$ of width $m>0$ by a constructor of arity $k$ yields a new matrix of width $k+m-1$.

*Some examples*. With $bold(P) = mat(A (1, 2), omega; omega, A (3, 4); B, B)$ we have

$
  bold(P) slash A = mat(1, 2, omega; omega, omega, A(3; 4)) #h(1cm) bold(P) slash B = mat(space; space) #h(1cm) bold(P) slash C^((3)) = mat(omega, omega, omega, A(3, 4))
$

Another example with negation :

$ mat(T(1, 2); not T(1, 2)) slash T = mat(1, 2; not 1, omega; omega, not 2) $

#columns(1, [

])

*Theorem(?)* We would like to have the following property $ bold(P) matches (A (v_11, ..., v_(1 k)), v_2, ..., v_m) space <==> space bold(P) slash A matches (v_1, ..., v_(1 k), v_2, ..., v_m) $

Intuitively, when we are looking at the matrix $bold(P) slash A$, we restrain the set of values matched by $bold(P)$ to those whose head constructor is $A$.

== Usefulness and exhaustivity

We now consider the problem of determining whether adding an extra row $arrow(q)$ to a matrix $bold(P)$ is _useful_, i.e. whether there are value rows unmatched by $bold(P)$, but matched by $arrow(q)$. Written and defined as :
$ cal(U)(bold(P), arrow(q)) <==> exists arrow(v). bold(P) refutes arrow(v) "and" arrow(q) matches arrow(v) $

The exhaustivity of a pattern matrix $bold(P)$ is thus expressed as property $not cal(U)(bold(P), (omega, ..., omega))$ which becomes $forall arrow(v). bold(P) matches arrow(v)$, and we claim this property is equivalent to our intuition of an exhaustive pattern-matching as seen in #ocaml.

*Theorems (for computation)*
$
  cal(U)(diameter, arrow(q)) &<==> exists arrow(v) | arrow(q) matches arrow(v) \
  cal(U)(mat(space; space), ()) &<==> bot \
  cal(U)(bold(P), (A(q_11, ..., q_(1 k)), q_2, ..., q_m)) &<==> cal(U)(bold(P) slash A, (q_11, ..., q_(1 k), q_2, ..., q_m)) \
  cal(U)(bold(P), (not r_1, q_2, ..., q_m)) &<==> cal(U)(bold(P) slash A plus.o (r_1, omega, ..., omega), (omega, q_2, ..., q_m)) \
  cal(U)(bold(P), (omega, q_2, ..., q_m)) &<==> exists C^((k)) in Sigma | cal(U)(bold(P) slash C, (omega, ..., omega, q_2, ..., q_m)) \ &#h(.5cm) "where" Sigma "is the signature of the first column of" bold(P) \
  cal(U)(bold(P), (r_1 or r_2, q_2, ..., q_m)) &<==> cal(U)(bold(P), (r_1, q_2, ..., q_m)) "or" cal(U)(bold(P), (r_2, q_2, ..., q_m)) \
  cal(U)(bold(P), (r_1 and r_2, q_2, ..., q_m)) &<==> cal(U)(bold(P), (r_1, q_2, ..., q_m)) "and" cal(U)(bold(P), (r_2, q_2, ..., q_m))
$

This gives a recursive algorithm to compute $cal(U)(bold(P), arrow(q))$.

*Optimizations*
In practice, when $q_1 = omega$, we cannot naively find a constructor $C in Sigma$ whose recursive call returns $top$, because $Sigma$ might be an infinite signature. An approach to eliminate recursive calls would be to look at the set $S$ of constructors appearing in the first column, then to check whether it forms a complete signature :
- if it is complete, then $S$ is a finite signature and we can loop over it to obtain our result.
- otherwise, we know there is at least one extra constructor not accounted for in the column, let it be called $C_"e"$. It suffices to loop over $S union.sq {C_e}$.

*Example* Let $bold(P) = mat(A; not B)$. If ${A^((0)), B^((0))}$ is a complete signature, the former case is applied. Otherwise, we get $ cal(U)(bold(P), omega) <==> underbrace(cal(U)(mat(space; space), ()), "spec. by" A) "or" underbrace(cal(U)(diameter, ()), "spec. by" B) "or" underbrace(cal(U)(mat(space; space), ()), "spec. by" C_e) $

and the result turns to to be $top$ thanks to the specialization by $B$.

In #ocaml, for the former case, we only need to specialize by $C_e$. But in the presence of a `not`-pattern, as seen in the previous example, we still need to specialize by the constructors who appear inside a negation pattern (modulo double negation). We can yet again refine the former case to only perform a minimal number of recursive calls. If $S^+$ is the set of constructors outside of a negation pattern (modulo double negation), and $S^-$ the set of those inside a negation pattern, then we get $S = S^+ union S^-$ :
- $S$ is a complete signature, we loop over $S$. (former case) _NOTE: maybe $S^+$ is enough!_
- otherwise, we loop over ${C_e} union S^- \\ S^+$. (latter case).

*Important distinction with #ocaml*

Consider now the case where we want to know $cal(U)(diameter, arrow(q))$. In $ocaml$, it is true that every pattern has at least one matching value, despite the existence of the empty type which is simply ignored @MARANGET_2007. In this case, there is no extra condition to check, and the algorithm simply returns $top$. However, as previously mentionned, it is now possible to intentionally write patterns with no matching value (such as $not omega$), so we technically need an extra check to make sure $q_1$ is not useless on its own.

A dubious solution would be to ignore this entirely and always return $top$, which doesn't actually cause any major problem. But it'd be nice to get a compiler warning (or error) whenever the user types in an impossible pattern.

*NOTE: difference between dnf and division algorithm?*

*NOTE: explicit value space decomposition lemma? more refined "finite sum" version?*

*NOTE: more general definition? $arrow(p) matches arrow(q)$ : $arrow(p)$ is "more general"*

#bibliography("references.bib")
