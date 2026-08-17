#let report(
  title: [],
  student: "",
  supervisor: "",
  date: "",
  logos: (),
  dep: "Computer Science Department",
  doc,
) = {
  // -------------------------------------- Generalities
  set page(
    paper: "a4",
    margin: (x: 3cm, y: 3cm),
  )
  set text(
    size: 12pt,
  )
  set heading(numbering: "1.")

  // -------------------------------------- Title page
  place(
    top + center,
    float: true,
    scope: "parent",
    clearance: 2em,
    {
      grid(
        columns: (2fr, 2fr, 2fr),
        align: (left, left, right),
        image("assets/ens_lyon.png", height: 40pt), image("assets/Logo_L1Ucb.png", height: 50pt),
      )

      // ---------------------------------- Institutions
      text(size: 16pt)[*École Normale Supérieure de Lyon*]
      text[\ *#dep*]

      // ---------------------------------- Title
      v(1cm)
      text(size: 30pt)[*L3 Research Internship Report*]
      v(1cm)
      line(length: 100%, stroke: (thickness: 3pt))
      text(size: 20pt, weight: "bold")[#title]
      line(length: 100%, stroke: (thickness: 3pt))

      // // ----------------------------------

      // ---------------------------------- People
      v(4fr)
      text(size: 16pt)[*Student*\ #student]
      v(4fr)
      text(size: 16pt)[*Supervised by*\ #supervisor]

      // ----------------------------------
      v(1cm)
      columns[
        #v(0.40cm)
        #image("assets/inr_logo_rouge.png", width: 80%)
        #colbreak()
        #v(0.25cm)
        #image("assets/Logo-irif.png", width: 60%)
      ]
      v(0.5cm)
      text[*Internship at INRIA and IRIF*]
      v(0.1cm)
      text[#date]
    },
  )

  outline(title: [Table of contents])

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
