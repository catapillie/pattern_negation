#let report(
  title: [],
  student: "",
  supervisor: "",
  date: "",
  logos: (),
  dep: "Computer Science Department",
  doc
) = {
  // -------------------------------------- Generalities
  set page(
    paper: "a4",
    margin: (x: 3cm, y: 3cm),
  )
  set text(
    size: 12pt
  )
  set heading(numbering: "1.")

  // -------------------------------------- Title page
  place(
    top + center,
    float: true,
    scope: "parent",
    clearance: 2em,
    {
      // ---------------------------------- Institutions
      text(size:16pt)[*École Normale Supérieure de Lyon*]
      text[\ *#dep*]

      // ---------------------------------- Title
      v(1cm)
      text(size:30pt)[*L3 Research Internship Report*]
      v(1cm)
      line(length:100%,stroke:(thickness:3pt))
      text(size:20pt,weight: "bold")[#title]
      line(length:100%,stroke:(thickness:3pt))

      // // ---------------------------------- ENS de Lyon logo
      v(1cm)
      image("assets/ens_lyon.png", width:25%)

      // ---------------------------------- People
      v(1fr)
      text(size:16pt)[*Student*\ #student]
      v(.5fr)
      text(size:16pt)[*Supervised by*\ #supervisor]
      v(1fr)

      // ---------------------------------- Date
      text[#date]

    }
  )

  outline(title:[Table of contents])

  pagebreak()
  counter(page).update(1)
  set page(
    paper: "a4",
    margin: (x: 3cm, y: 3cm),
    numbering: "1/1",
  )

  doc

  bibliography("references.bib", style: "./gasche-author-date.csl")

}
