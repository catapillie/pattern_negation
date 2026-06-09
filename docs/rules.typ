#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/showybox:2.0.4": showybox

= Inference rules for pattern-matching

#let matches = $prec.eq$
#let incomp = $prec.eq.not$

Instead of defining a pattern-matching relation $p prec.eq v$ between patterns and values, we can define a relation $p matches q$ between patterns with syntactic rules. Intuitively, $p matches q$ means that $p$ is more general than $q$. This generalization makes sense because every value can be seen as a pattern. Because of pattern negation, we'll also have to give an inductive definition of $p incomp q$, the negation of $p matches q$

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
        $p incomp q_1 or q_2$,
      )),
      prooftree(rule(
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
        $p incomp not q$,
      )),
    ),
  )

]

*Theorem*. $matches$ is a preorder.
