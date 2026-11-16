#import "@preview/trivial:0.1.0"
#show: trivial.init

// #let definition = trivial.theorem.with(
//  "definition",
//  trivial.styles.theorem.default,
//  [Definition],
// )
// [AI-edited (claude-opus-5-5), 2026-11-15, at the author's request: definitions, theorems and the
// other environments are numbered <section>.<number in section>; the counter restarts at every
// top-level heading through `theorems-per-section`, which deep+.typ applies with a show rule.
// Please review]
//
// All environments are figures of kind "theorem", so they share one counter (Definition 3.1,
// Lemma 3.2, Theorem 3.3, ...). The numbering function prefixes the number of the current
// top-level section; it runs at the location of the environment, also when a reference
// (@label) displays the number, so references get the same "3.2".
#let numbered-theorem = trivial.theorem.with(
  "theorem",
  trivial.styles.theorem.default,
  numbering: (..nums) => numbering("1.1", counter(heading).get().first(), ..nums),
)

// Restart the shared counter at every top-level heading. Use it as `#show: theorems-per-section`
// in the document (a show rule written in this file would not reach the files that import it).
#let theorems-per-section(doc) = {
  show heading.where(level: 1): it => {
    counter(figure.where(kind: "theorem")).update(0)
    it
  }
  doc
}
#let definition = numbered-theorem.with([Definition])
#let theorem = numbered-theorem.with([Theorem])
#let lemma = numbered-theorem.with([Lemma])
#let corollary = numbered-theorem.with([Corollary])
#let remark = numbered-theorem.with([Remark])
#let construction = numbered-theorem.with([Construction])
#let example = numbered-theorem.with([Example])

#let qed = sym.square
#let proof = trivial.proof.with(
  [Proof],
  (title, body) => block(width: 100%, below: 2em)[_#title._ #body],
  qed: $qed$,
)