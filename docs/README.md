## Docs

Everything regarding the intership report is in [`./report/`](./report/).

Formal description of different approaches to study pattern-matching exhaustivity and analysis in the presence of `not`-patterns. The documents were written the the Typst language, which can thus be compiled with the following command:
```sh
typst compile <doc.typ>
```

Descriptions of the files
- [`overview.typ`](./overview.typ) : initial attempt at extending pattern-matching with pattern negation. The approach described here is the one used for the implementation of [`pmcomp`](../pmcomp/).

- [`inclusion.typ`](./inclusion.typ) : a different approach at solving exhaustivity using an inclusion relation between patterns. The file contains mostly the inference rules properly formatted, however the approach did not lead to any major breakthrough. See comments in [`../proof/README.md`](../proof/README.md).

- [`typing.typ`](./typing.typ) : this is the main document written which served as a base for the internship report.