#import "@preview/diatypst:0.8.0": *
#show: slides.with(
  title: "Elementary Model Theory in Rocq",
  subtitle: "Current Progress Report",
  date: "Tuesday, December 9 2025",
  authors: ("Jeffery","Sai","David"),
  layout: "large",
  title-color: orange.darken(80%),
  count: "number",
  theme: "full",
  toc: false,
)
#set text(size: 14pt)

= Introduction
== What even is "Model Theory?"
\
The study of Mathematical "models" and their capabilities, interpretations, and theories. \
_Models?_
- Formulas
- Languages
- Sentences
- What are they composed of?
- How do we write things down?
Idea: Given a language, a sentence, and a theory, what does it mean? Is the theory valid? Are there some things which cannot be proven in this language?
== Goal
\
- Implement Elementary Model Theory in Rocq
    - Gödel's First Incompleteness Theorem
    - Łoś's Theorem (ultraproducts)
    - Löwenheim–Skolem Theorem
    - Concerning completeness/compactness
    - Stability
\
Proofs requires non-trivial definitions, theorems and lemmas.

== What Already Exists
From what he have seen, it is very difficult to find Model Theory libraries and or implementations in Rocq.
- Why?
== Approach
\ 
- Define primary concepts and syntax.
- State lemmas and work upwards towards desired theorem.
- Restrictions on `Stdlib`
= Our Progress
== Sections & Definitions
Definitions so Far:
- First-order language: $cal(L)$
  - Logical symbols of $cal(L)$: $sans("Var"), =^., and, or, not, ->, <-->, forall, exists$
  - Signature of $cal(L)$: $sans("Const")(cal(L)), sans("Rel")(cal(L)), sans("Fun")(cal(L))$
- Terms of $cal(L)$ or $cal(L)$_-terms_
- Formulas of $cal(L)$ or $cal(L)$_-formulas_
\
Sections:
- Languages
- Semantics
== Difficulties
\ \
- Translating definitions into Rocq:
  - Enforcing properties?
- Weak definitions and or induction schema
- Proving simple things are hard
- Proving in Rocq requires deep knowledge of proof.
  - Learning Model Theory
- Getting stuck

= What's Next
== Readjusting Expectations
Fallbacks:
- Focus on most important results:
  - Gödel's Results
  - Completeness/Compactness

== Takeaways
\ \
- Rocq's "Limitations"
- No Sandboxing
- Acknowledging Previous Efforts
\ \
😾
