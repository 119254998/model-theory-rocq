#set page("a4", numbering: "1")
#set text(size: 12pt)
#align(center)[
  #text(size: 22pt)[#smallcaps("CMSC631 Final Project Report")] \
  #text(size: 14pt)[Jeffery, Sai & David] \
  #text(size: 12pt)[Fall 2025] \
]

Code: https://github.com/119254998/model-theory-rocq

= Objective
Initially, we wanted to prove the big results in Model Theory: Gödel's First Incompleteness Theorem, Łoś's Theorem, and Löwenheim–Skolem Theorem. We decided we would focus primarily on Gödel's First Incompleteness if we did not make sufficient progress. Since the result does not need as many definitions, theorems, or lemmas. \

We picked this project since we did not see much Model Theory formalization out there, especially in Rocq. We initially considered doing it in Lean, since it is more adopted for Math formalization than Rocq. We did not end up doing that to avoid having to learn both Model Theory and Lean at the same time. Which did not seem feasible given the project's timeframe. \ 

In the end, we opted to work towards an implementation of FOL using Kripke-style semantics, and proving soundness, completeness and compactness.
= Results
We were unable to make much progress on our initial goal of proving compactness + completeness in first order logic, as it used Tarski's structure, which was much more complicated to work with. We were able to define many basic facts and state some important lemmas about formulas and sentences. This is due to the difficulty in defining terms, and having a good induction scheme that can work to prove all of the relevant theorems and substitution lemmas. In order to get around this, we opted to use a different encoding by Kripke. However, this new encoding meant that we had to re-learn model theory in this new encoding, which was very difficult. At the end, we were able to prove soundness, completeness and compactness assuming the correctness of various substitution lemmas for the encoding of the Kripke encoding of FOL. To our knowledge, this is the first time these results have been proved in Rocq, as we could only find encodings of FOL in the Kripke style, but could not find any actual proofs of soundness, compactness or completeness. 
= Difficulties
== Model Theory
Some of the group picked this project with the goal of learning Model Theory along the way. This ended up being a bigger hurdle than one would have imagined. Mainly because of the time commitment to consuming information and retaining it, but also because formalizing elementary Model Theory requires a lot deeper of an understanding than one would have thought. There are multiple ways of proving our desired theorems in Math, but we did not really have enough awareness to be able to pick a system which would lend itself well to Rocq. Dealing with all of the different substitution lemmas and making sure that we could satisfy Rocq made proofs much much longer. Another major difficulty was switching from Tarski to Kripke-style semantics which meant that we had to relearn a lot of the model theory as it was quite unfamiliar and there wasn't a lot of results in this area.
== Satisfying Proof Goals
A huge hurdle was actually being able to prove things about our definitions. Even simple Lemmas which follow directly from definitions were hard to prove due to weak definitions. Eventually, we decided to overhaul our project from the ground up, in order to have stronger definitions. Then we ran into the issue of getting stuck writing definitions. In order to get around this, we `Admitted` a lot of lemmas regarding substitution or other technical conerns so that we could prove our main goal of completeness and compactness. 
== Non-Trivial Construction
It's worth noting that we have a lot of _unused_ definitions. This is because we did not get around to proving things about every definition, or even constructing examples.  This is because translating a mathematical definition into a valid Rocq implementation is quite difficult. Representing invariants is not obvious in Rocq, such as if a set $S != nothing$. Or how $sans("Const")$ should have been encoded in our records. We ended up with _no_ explicit Constants type/set, since we could embed them in functions as functions with no arguments. 

