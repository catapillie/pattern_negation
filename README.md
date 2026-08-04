### Pattern negation

Various works on extension OCaml-like pattern matching with `not`-patterns. A pattern `not p` matches iff `p` does not match. The intersection pattern (or "and"-pattern) is also introduced : `p1 & p2` matches iff `p1` and `p2` both match. 

- [`docs/`](/docs/): paper, notes and the report.
- [`pmcomp/`](/pmcomp/): Implementation of pattern negation, compilation and exhaustivity with minimal toy language.
- [`proof/`](/proof/): (attempts of) formalization in the Rocq proof assistant.
