#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/showybox:2.0.4": showybox

= Inference rules for pattern-matching

#let matches = $>=$
#let incomp = $#h(.2em) hash #h(.2em)$

Instead of defining a pattern-matching relation $p succ.eq v$ between patterns and values, we can define a relation $p matches q$ between patterns with syntactic rules. Intuitively, $p matches q$ means that $p$ is more general than $q$. This generalization makes sense because every value can be seen as a pattern.

Because of pattern negation, we'll also have to handle the case for $not p matches q$, which is intuitively equivalent to the fact that $p$ and $q$ are _incompatible_, written $p incomp q$.

#showybox[
  *$p matches q$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $omega matches p$,
      )),
      prooftree(rule(
        $p_1 matches q_1$,
        $dots.c$,
        $p_n matches q_n$,
        $A(p_1, ..., p_n) matches A(q_1, ..., q_n)$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $p_1 matches q$,
        $p_1 or p_2 matches q$,
      )),
      prooftree(rule(
        $p_2 matches q$,
        $p_1 or p_2 matches q$,
      )),
      prooftree(rule(
        $p matches q_1$,
        $p matches q_2$,
        $p matches q_1 or q_2$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $p_1 matches q$,
        $p_2 matches q$,
        $p_1 and p_2 matches q$,
      )),
      prooftree(rule(
        $p matches q_1$,
        $p matches q_1 and q_2$,
      )),
      prooftree(rule(
        $p matches q_2$,
        $p matches q_1 and q_2$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $p incomp q$,
        $not p matches q$,
      )),

      prooftree(rule(
        $not p incomp not q$,
        $p matches not q$,
      )),
    ),
  )

]


#showybox[
  *$p incomp q$*

  #align(
    center,
    rule-set(
      prooftree(rule(
        $A(p_1, ..., p_n) incomp B(q_1, ..., q_m)$,
      )),
      prooftree(rule(
        $p_i incomp q_i$,
        $1 <= i <= n$,
        $A(p_1, ..., p_n) incomp A(q_1, ..., q_n)$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $p_1 incomp q$,
        $p_2 incomp q$,
        $p_1 or p_2 incomp q$,
      )),
      prooftree(rule(
        $p incomp q_1$,
        $p incomp q_2$,
        $p incomp q_1 or q_2$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $p_1 incomp q$,
        $p_1 and p_2 incomp q$,
      )),
      prooftree(rule(
        $p_2 incomp q$,
        $p_1 and p_2 incomp q$,
      )),
      prooftree(rule(
        $p incomp q_1$,
        $p incomp q_1 and q_2$,
      )),
      prooftree(rule(
        $p incomp q_2$,
        $p incomp q_1 and q_2$,
      )),
    ),
  )

  #align(
    center,
    rule-set(
      prooftree(rule(
        $p matches q$,
        $not p incomp q$,
      )),
      prooftree(rule(
        $q matches p$,
        $p incomp not q$,
      )),
    ),
  )

]

*Theorem* $matches$ is reflexive and transitive.

*Corollary* For all patterns $p$ and $q$ :
$ p matches q space <==> space forall v, q matches v => p matches v $
We claim this reformulation of the relation $matches$ is one that matches our intuition of patterns being more general than others, and more specifically if the right-hand side is restrained to values, then it _is_ the definition of pattern matching in @MARANGET_2007.

*Theorem* $hash$ is irreflexive and symmetric.

#pagebreak()
#bibliography("references.bib")
