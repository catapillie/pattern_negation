## `pmcomp`

Implementation of pattern negation, compilation and exhaustivity with minimal toy language.

The project is built with `dune build`.
Usage:
```sh
./pmcomp <path>
```

### Syntax
Patterns are terms defined with the following grammar
```
p := _                    (wildcard)
   | C(p1, ..., pn)       (constructor) n>= 0
   | ~p                   (negation)
   | p | q                (disjunction)
   | p & q                (conjunction)
   | (p)                  (parentheses)

   | (p1, p2, ..., pn)    (tuple) n != 1
       is an alias for `tupn(p1, p2, ..., pn)`
```

A finite complete signature can be defined by
```
sig C1, ..., Cn ;; 
```

The expected syntax read by the program is a list of signature definitions immediately followed by
```pm
switch
    case p1
    ...
    case pn
;;
```

*Example*
```pm
sig tup2 ;;
sig A, B ;;

switch
    case  (A | ~B(1, 2))
    case ~(A | ~B(1, 2))
;;
```

### Behavior

Given a syntactically valid input, the program checks if the given pattern-matching problem is exhaustive, after which one of two following messages is shown :
- `Pattern-matching is partial.`
- `Pattern-matching is exhaustive.`

The program then compiles the pattern-matching into a minimal "lambda-code"-style expression, similar to [OCaml's `lambda` IR](https://github.com/ocaml/ocaml/blob/trunk/lambda/lambda.mli). The output is then printed, after going through a naive optimization pass (for instance, by eliminating chains of the forl raise-catch-raise-... and so on).
