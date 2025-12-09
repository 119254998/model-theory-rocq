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
#set text(size: 16pt)

= Introduction
== What even is "Model Theory?" 
\
  In math, we study different types of structures and how they interact with others \ \ For example: group theory is the study of Groups, and field theory is the study of Fields \ \ Model theory is the study of mathematical structures as a whole

== What is a "Model"?
\ 
  A model is a representation of a mathematical theory \ \ A mathematical theory is a collection of axioms - formal statements in a language \ \ Let's consider groups as a simple example

== What is a "Model"?
\ 
  A "group" is a set, G, along with a multiplication function $dot.o : G times G arrow G$ that obeys the following axioms:
  - $forall a,b,c in G, a dot.o (b dot.o c) = (a dot.o b) dot c$
  - $exists e$ such that $forall a in G, e dot.o a = a dot.o e = a$
  - $forall a in G, exists b$ such that $a dot.o b = b dot.o a = e$

== What is a "Model"?
\ 
  One model of a group would be $ZZ$ - the integers \  \ One can check it obeys all the axioms \ \ Model theory is about arbitrary collections of functions, axioms and their models \ \ Questions we want to answer are "what can we prove using these axioms?" and "is a given theory consistent?"

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
\
We have the basics of Peano arithmetic in the Rocq standard library
\
\
Additionally, there was a crowdsourced effort that ended \~3 years ago which was able to prove Godel's first incompleteness theorem: https://github.com/rocq-community/goedel/

From what he have seen, it is very difficult to find Model Theory libraries and or implementations in Rocq.
- Why?
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
