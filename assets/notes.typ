// small collection of 445 notes for quick reference
// and also so they can be gathered in one place
// credit:
// aris papadopoulos's math 445 notes
// https://arispapadopoulos.github.io/teaching/445.html

#set page(numbering: "1")
#set text(font: "New Computer Modern", size: 12pt)
// #set math.mat(delim: "[")
// #set math.vec(delim: "[")
// #set enum(numbering: a => strong[#numbering("a.", a)])

#show list.item: it => {
  if it.has("label") and it.label == <processed> { return it }
  [#list.item(it.body + h(1fr))<processed>]
}
#show enum.item: it => {
  if it.has("label") and it.label == <processed> { return it }
  [#enum.item(it.body + h(1fr))<processed>]
}

#let span = "span"
#let dim = "dim"
#let rank = "rank"
#let mapsto = sym.mapsto.long
#let iff = sym.arrow.l.r.double.long
#let qed = context block(width: 100%, align(right, $square$))
#let contra = context block(width: 100%, align(right, $times.circle.big$))
#let iffs(a, b) = list(block[( $==>$ ) \ #a], block[( $<==$ ) \ #b] )
#let inner(x, y) = $lr(angle.l #x, #y angle.r)$
#let minor(..x) = $mat(gap: #0.6em, delim: "|", ..#x)$
#let ord(sub:[], x) = {if sub!=[]{$"ord"_#sub (#x)$}else{$"ord"(#x)$}}
#let inv(x) = $#x^(-1)$
#let problem(num, body) = block(width: 100%,radius: 5pt,inset: 8pt,fill: luma(235))[*Problem #num:* #body]
#let def(name, body, num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[*Definition#{if num!=[]{[ #num]}else[]}: #name*\ #body]
#let thm(body, name:[], num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[#context[*Theorem#{if num!=[]{[ #num]}else[]}: #{if name!=[]{[#name\ ]}else[]}*]#body]
#let lemma(body, name:[], num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[#context[*Lemma#{if num!=[]{[ #num]}else[]}: #{if name!=[]{[#name\ ]}else[]}*]#body]
#let cor(body, name:[], num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[#context[*Corollary#{if num!=[]{[ #num]}else[]}: #{if name!=[]{[#name\ ]}else[]}*]#body]
#let ex(body, name:[], num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[#context[*Example#{if num!=[]{[ #num]}else[]}: #{if name!=[]{[#name\ ]}else[]}*]#body]
#let exercise(body, name:[], num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[#context[*Exercise#{if num!=[]{[ #num]}else[]}: #{if name!=[]{[#name\ ]}else[]}*]#body]
#let remark(body, name:[], num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[#context[*Remark#{if num!=[]{[ #num]}else[]}: #{if name!=[]{[#name\ ]}else[]}*]#body]
#let hist(body, name:[], num:[]) = block(width:100%,radius:5pt,inset:8pt,fill:luma(235))[#context[*History#{if num!=[]{[ #num]}else[]}: #{if name!=[]{[#name\ ]}else[]}*]#body]
#let proof(body) = context block(width:100%,stroke:(left:2pt+luma(200)),inset:(left: 8pt))[_Proof:_ #body]
#let solution(body) = context block(width:100%,stroke:(left:2pt+luma(200)),inset:(left: 8pt))[_Solution:_ #body]
#let ded(x) = $attach(tack.r, br: #x)$
#let restrict(x) = $attach(harpoon.tr, br: #x)$
#let phi = $phi.alt$
#let modelsnot = $tack.r.double.not$
#let Var = $sans("Var")$
#let Sub = $sans("Sub")$
#let val = $sans("val")$
#let supp = $sans("supp")$
#let Const = $sans("Const")$
#let Rel = $sans("Rel")$
#let Fun = $sans("Fun")$
#let arity = $sans("arity")$
#let Free = $sans("Free")$
#let Bound = $sans("Bound")$

// #align(center)[= #smallcaps([Homework X])]
== Week 2
#def[Formulas][
  $
    sans("Var") := "set of all propositional variables"
  $
  A *formula of propositional logic* is inductively built, as follows:
  + A propositional variable is a formula.
  + If $phi$ and $psi$ are formulas, then so are:
    + $(phi and psi)$
    + $(phi or psi)$
    + $(phi -> psi)$
    + $(not phi)$
  + Every propositional formula is finite and built this way.
]
#ex[
  $A, B in sans("Var")$:
  $
    (A and B), (A or B), ((not(A and B)) -> ((not A) or (not B))).
  $
  For now, these formulas are only syntactical objects, there is no meaning.
]
#def[Subformulas][
  Let $phi$ be a formula. We define the set of subformulas of $phi$, denoted $sans("Sub")(phi)$ inductively, as follows:
  + For $A in sans("Var")$: $sans("Sub") = {A}$
  + Suppose $sans("Sub")(phi_1)$ and $Sub(phi_2)$ are defined, then:
    - $Sub(phi_1 and phi_2) = {phi_1 and phi_2} union Sub(phi_1) union Sub(phi_2)$
    - $Sub(phi_1 or phi_2) = {phi_1 or phi_2} union Sub(phi_1) union Sub(phi_2)$
    - $Sub(phi_1 -> phi_2) = {phi_1 -> phi_2} union Sub(phi_1) union Sub(phi_2)$
    - $Sub(not phi_1) = {not phi_1} union Sub(phi_1)$
  We say $psi$ is a _proper subformula_ of $phi$ if $psi in Sub(phi) \\ {phi}$.
]
#def[$Var(phi)$][
  Let $phi$ be a formula, the _set of variables of $phi$_ denoted by $Var(phi)$ is defined inductively, as follows:
  + For $A in Var$, define $Var(A) = {A}$.
  + Suppose $Var(phi_1)$ and $Var(phi_2)$ are defined, then:
    - $Var(phi_1 and phi_2) = Var(phi_1) union Var(phi_2)$
    - $Var(phi_1 or phi_2) = Var(phi_1) union Var(phi_2)$
    - $Var(phi_1 -> phi_2) = Var(phi_1) union Var(phi_2)$
    - $Var(not phi_1) = Var(phi_1)$
]
#def[Substitution][
  Let $phi, psi$ be formulas and $A in Var$. The _substition of $psi$ for $A$ in $phi$_, denoted $phi[psi\/A]$ is defined as follows:
  + For $B in Var$ we define $B[psi\/A]$ as:
    $
      B[psi\/A] := cases(B &"  if" A != B, psi &"  if" A = B)
    $
  + Suppose $phi_1[psi\/A]$ and $phi_2[psi\/A]$ are defined, then:
    - $(phi_1 and phi_2)[psi\/A] = (phi_1[psi\/A] and phi_2[psi\/A])$
    - $(phi_1 or phi_2)[psi\/A] = (phi_1[psi\/A] or phi_2[psi\/A])$
    - $(phi_1 -> phi_2)[psi\/A] = (phi_1[psi\/A] -> phi_2[psi\/A])$
    - $(not phi_1)[psi\/A] = (not phi_1[psi\/A])$
]
#lemma[
  Suppose $A in.not Var(phi)$. Then $phi[psi\/A] = phi$ for any formula $psi$.
]
#def[Truth Functions][
  $
    T := "Truth" \
    F := "Falsity" \
  $
  $
    f: {T, F}^x -> {T, F}, x in ZZ
  $
]
#def[Assignment][
  A _truth assignment_ (or just _assignment_) is a function $cal(A)$ which associates to every propositional variable a truth value, i.e. a function $cal(A): Var -> {T, F}$. We will write $bb(A)$ for the set of all assignments.
]
#def[Valuation][
  Let $phi$ be a propositional formula and $cal(A)$ an assignment. Then, the _valuation of $phi$ under $cal(A)$_, denoted $val_cal(A) (phi)$ is defined as follows:
  + $val_cal(A) (A) = cal(A)(A)$ for any $A in Var$
  + Let $phi_1$ and $phi_2$ be propositional sentences and assume that $val_cal(A) (phi_1)$ and $val_cal(A) (phi_2)$ have been defined, then:
    + $val_cal(A) (phi_1 and phi_2) = f_(and)(val_(cal(A))(phi_1), val_(cal(A))(phi_2))$
    + $val_cal(A) (phi_1 or phi_2) = f_(or)(val_(cal(A))(phi_1), val_(cal(A))(phi_2))$
    + $val_cal(A) (phi_1 -> phi_2) = f_(->)(val_(cal(A))(phi_1), val_(cal(A))(phi_2))$
    + $val_cal(A) (not phi_1) = f_(not)(val_(cal(A))(phi_1))$
  We will also write $phi[cal(A)]$ to denote $val_(cal(A))(phi)$ and we will write $cal(A) models phi$ to denote that $phi[cal(A)] = T$ (and similarly $A modelsnot phi$ to denote that $phi[A] = F$)
]
#thm(name: "2.2.4")[
  Let $phi$ be a formula and $cal(A), cal(B) in AA$. Suppose that for all $A in Var(phi)$ we have that $cal(A)(A) = cal(B)(A)$. 
  $
    "Then" A models phi iff B models phi
  $
]
#def[Tautology][
  We say a formula $phi$ is a _tautology_, if for all $cal(A) in AA$ we have that $cal(A) models phi$. In this case we write $models phi$.
]
#def[Logically Entails][
  We say that a formula $phi$ _logically entails_ a formula $psi$ if, for every $cal(A) in AA$ such that $phi[cal(A)] = T$ we have that $psi[cal(A)] = T$. In this case, we write $phi models psi$. More generally, if $Gamma = {phi_1, ..., phi_n, ...}$, we say that $Gamma$ _logically entails_ a formula $psi$ if, for every $cal(A) in AA$ such that $phi_i [cal(A)] = T$ for all $phi_i in Gamma$ (at the same time) we have that $psi[cal(A)] = T$. In this case, we write $Gamma models psi$.
]
#def[$<->$][
  Define $f : {T, F}^2 -> {T, F}$ by:
  #align(center)[#table(columns: 3, stroke: .05em,
    $x$, $y$, $f(x, y)$,
    $F$, $F$, $T$,
    $F$, $T$, $F$,
    $T$, $F$, $F$,
    $T$, $T$, $T$,
  ) ]
  $<->$ is defined for each $cal(A) in AA$:
  $
    (phi_1 <-> phi_2)[cal(A)] := f(phi_1 [cal(A)], phi_2 [cal(A)]).
  $
  That's to say for any $cal(A) in AA$ we have:
  $
    (phi_1 <-> phi_2)[cal(A)] = f(phi_1 [cal(A)], phi_2 [cal(A)]) = cases(
      T &"   if" phi_1 [cal(A)] = phi_2 [cal(A)],
      F &"   if" phi_1 [cal(A)] != phi_2 [cal(A)],
    )
  $
  In this sense, any function $f : {T, F}^n -> {T, F}$ defines a new connective (not all of them deserve their own symbols though)
]
#def[Logically Equivalent][
  We say that a formula $phi$ is _logically equivalent_ to a formula $psi$ if $phi <-> psi$ is a _tautology_.
]
#lemma[
  Let $phi$ and $psi$ be formulas. Then, the following are equivalent:
  + $phi$ logically implies $psi$.
  + $(phi -> psi)$ is a tautology.
  In symbols, $phi models psi iff models (phi -> psi)$
]
#def[Unsatisfiable][
  A formula $phi$ is called _unsatisfiable_ (or _contradictory_) if for all $cal(A) in AA$ we have that $phi[cal(A)] = F$. We say that a set of formulas $Gamma$ is _unsatisfiable_ if for all $cal(A) in AA$ there is some $phi in Gamma$ such that $phi[cal(A)] = F$. \ \
  Clearly, $phi$ is contradictory if and only if $not phi$ is a tautology.
]
#lemma[
  Let $Gamma$ be a set of formulas and $phi, psi$ be formulas. If $Gamma$ logically entails $(phi -> psi)$ and $phi$, then $Gamma$ logically entails $psi$. In particular if $phi$ and $phi -> psi$ are tautologies, then so is $psi$. \ \
  In symbols, if $Gamma models phi$ and $Gamma models (phi -> psi)$ then $Gamma models psi$.
]
#def[Truth Function][
  A function $f : AA -> {T, F}$ is called a truth function if there exists a finite set of variables ${A_1, ..., A_n} subset.eq Var$ such that for all assignments $cal(A), cal(B)$ we have that if:
  $
    cal(A)_i restrict({a_1, ..., A_n}) = cal(B) restrict({A_1, ..., A_n})
  $
  Then, $f(cal(A)) = f(cal(B))$. In this case, we call $A_1, ..., A_n$ the _support_ of $f$, denoted $supp(f)$
]
#def[$cal(F)$-term][
  Let $cal(F) := {f_1 : {T, F}^(n_1) -> {T, F}, ..., f_k : {T, F}^(n_k) -> {T, F}}$ be a set of trith functions. An _$cal(F)$-term_ is defined, inductively, as follows:
  + Any propositional variable $A_n$ is an $cal(F)$-term.
  + For each $f_i in cal(F)$, and $cal(F)$-terms $t_1, ..., t_n$, $f_i (t_1, ..., t_(n_i))$ is an $cal(F)$-term.
  + All $cal(F)$-terms are built like this
]
#lemma[
  $cal(F) := {f_1 : {T, F}^(n_1) -> {T, F}, ..., f_k : {T, F}^(n_k) -> {T, F}}$ be a set of truth functions and $h$ an $cal(F)$-term. Then $h$ defines a truth function.
]
#def[Adequate][
  Let $cal(F)$ be a set of truth functions. We say that $cal(F)$ is _adequate_ if for all $n in NN$, evert truth function $g : {T, F}^n -> {T, F}$ can be written as a composition of functions from $cal(F)$.
]
#cor[
  Let $phi$ be a propositional formula. Then, there is a propositional formula $psi$ of the form:
  $
    or.big_(i = 1)^l (and.big_(j = 1)^m A_(i, j) and and.big_(j = 1)^n not B_(i, j))
  $
  where $A_(i, j)$ and $B_(i, j)$ are propositional variables, such that $phi$ and $psi$ are logically equivalent.
]
== Week 3a
=== Axioms:
- (A1) $(phi -> (psi -> phi))$
- (A2) $((phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> psi)))$
- (A3) $(phi -> (psi -> phi))$
=== Deduction Rules:
- 
  (MP) #smallcaps[Given]: $phi -> psi$ and $phi$ \
  $"       "$ #smallcaps[Deduce]: $psi$ // #smallcaps doesn't work in math mode?
#def[Formal Proof, Theorem, Deducible][
  A *formal proof* of formula $phi$ is a finite sequence:
  $
    (phi_1, ..., phi_n)
  $
  of formuls such that $phi_n = phi$ for each $i <= n$, one of the following holds:
  - Either $phi_i$ is an instance of an axiom
  - Or $phi_i$ can be deduced from an instance of (MP) for some $j, k < i$.
  If there is a formal proof of $phi$, we write $tack.r phi$, and call $phi$ a *theorem*. \
  More generally, let $Gamma$ be a set of formulas. We say that $phi$ is *deducible* from $Gamma$ if there's a finite sequence:
  $
    (phi_1, ..., phi_n)
  $
  of formulas such that $phi_n = phi$ and for each $i <= n$, one of the following holds:
  - Either $phi_i$ is an instance of an axiom
  - Or $phi_i in Gamma$
  - Or $phi_i$ can be deduced from an instance of (MP) for some $j, k < i$.
  In this case we write $Gamma tack.r phi$.
]
#thm(name: "Soundness of Predicate Logic")[
  If $Gamma tack.r psi$, then $Gamma models psi$. In particular, every theorem is a tautology.
]
#thm(name: "Completeness of Predicate Logic")[
  If $Gamma models psi$, then $Gamma tack.r psi$. In particular, every theorem is a tautology.
]
#lemma[
  The following are equivalent:
  + $Gamma tack.r (phi -> psi)$
  + $Gamma union {phi} tack.r psi$
]
#def[Inconsistent][
  A set of formulas $Gamma$ is _inconsistent_ if there's a formula $phi in Gamma$ such rhat $Gamma tack.r phi$ and $Gamma tack.r not phi$. Otherwise, if no such $phi$ exists, we say that $Gamma$ is _consistent_.
]
#lemma(name: "(The Adequacy Theorem)")[
  If $Gamma$ is _unsatisfiable_, then $Gamma$ is _inconsistent_.
]
#cor(name: "(Propositional Compactness)")[
  Let $Gamma$ be a set of propositional formulas. Then, the following are equivalent:
  + $Gamma$ is satisfiable.
  + Every finite subset of $Gamma$ is satisfiable.
]
#cor(name: "(Decidability of Propositional Logic)")[
  There is an $"algorithm"r$ which given a finite set of propositional formulas $Gamma$ and a formula $phi$ determines whether or not $Gamma tack.r phi$.
  \
]
== Week 3b
#def[First-order Language][
  A _first-order language_ is a set of symbols $cal(L)$ which consists of two disjoint subsets:
  + The _logical symbols_ of $cal(L)$:
    + A countable set of _variables_ $Var$, which we denote by $x, x_1, x_2, ..., y, y_1, y_2, ..., z, z_1, z_2, ..., "etc"$
    + Classical logic symbols: $and, or, not, ->, <->, forall, exists$.
    + A symbol for equality $eq^.$.
  + The _signature_ of $cal(L)$ (the _non-logical_ symbols of $cal(L)$), these are the following three #underline[disjoint] sets:
    + A set of _constant symbols_ $Const(cal(L))$. We usually denote (abstract) constant symbols as $underline(c), underline(c)_1, underline(c)_2, ....$
    + A set of _relation symbols_ $Rel(cal(L))$. We will usually denote (abstract) relation symbols as $underline(R), underline(R)_1, underline(R)_2, ....$
    + A set of _function symbols_  $Fun(cal(L))$. We will usually denote (abstract) function symbols as $underline(f), underline(f)_1, underline(f)_2, ....$.
    As part of the signature we also have an _arity_ function:
    $
      arity_(cal(L)) : Rel(cal(L)) union.sq Fun(cal(L)) -> NN_(>= 1)
    $
    Let $underline(R) in Rel(cal(L))$. If $arity(underline(R)) = n$ then we say that $underline(R)$ is an $n$-ary relation symbol. Similarly, if $underline(f) in Fun(cal(L))$, and $arity(underline(f)) = n$ then we say that $underline(f)$ is an $n$-ary function symbol.
]
#def[$cal(L)$-term][
  Let $cal(L)$ be a first-order language. The _terms_ of $cal(L)$ or $cal(L)$-terms are defined inductively, as follows:
  + Every variable is an $cal(L)$-term.
  + Every constant $underline(c) in Const(cal(L))$ is an $cal(L)$-term.
  + If $underline(f) in Fun(cal(L))$ is an $n$-ary function symbol and $t_1, ..., t_n$ are $cal(L)$-terms, then $underline(f)(t_1, ..., t_n)$ is an $cal(L)$-term.
]
#remark[
  Relation symbols don't show up in term building.
]
#lemma(num: "1.1.4")[
  Let $cal(L)$ be a first-order language. Let $cal(T)_0$ be the set $Var(cal(L)) union Const(cal(L))$. Inductively, define $cal(T)_(n + 1)$ to be the set:
  $
    cal(T)_(n + 1) := cal(T)_n union {underline(f)(t_1, ..., t_k) : k in NN, underline(f) in Fun(cal(L)), arity(underline(f)) = k, t_i in cal(T)_n},
  $
  and let $cal(T) = union.big_(n in NN) cal(T)_n$. Then $cal(T)$ is the set of all $cal(L)$-terms.
]
#def[Atomic $cal(L)$-formulas][
  The _atomic formulas_ of $cal(L)$ (or _atomic $cal(L)$-formulas)_ are defined inductively as follows:
  + If $t_1, t_2$ are $cal(L)$-terms, then $t_1 =^. t_2$ is an atomic $cal(L)$-formula.
  + If $underline(R) in Rel(cal(L))$ is an $n$-ary relation. Symbol and $t_1, ..., t_n$ are terms, then $underline(R)(t_1, ..., t_n)$ is an atomic $cal(L)$-formula.
]
#def[$cal(L)$-formulas][
  The _formulas_ of $cal(L)$ (or $cal(L)$-formulas) are defined inductively, as follows:
  + Every atomic $cal(L)$-formula is an $cal(L)$.
  + If $phi$ and $psi$ are $cal(L)$-formulas, and $x in Var$, then:
    #columns(3)[
      $(phi and psi)$ #colbreak()
      $(phi or psi)$ #colbreak()
      $(phi -> psi)$ #colbreak()
      $(not psi)$ #colbreak()
      $(forall x)phi$ #colbreak()
      $(exists)phi$
    ]
    are all $cal(L)$-formulas.
  + That's it - all $cal(L)$ formulas are constructed by finitely many applications of (1) and (2).
]
#def[$Var(t)$][
  Let $cal(L)$ be a first-order language and $t$ an $cal(L)$-term. We define the _set of variables of $t$_, denoted $Var(t)$, as follows:
  + If $t$ is the variable $x$ then $Var(t) = {x}$.
  + If $t$ is a constant symbol, then $Var(t) = emptyset$.
  + If $t$ is of the form $underline(f)(t_1, ..., t_n)$ for some $n$-ary function symbol $underline(f) in Fun(cal(L))$ and $cal(L)$-terms $t_1, ..., t_n$m then $Var(t) = union.big_(i <= n) Var(t_i)$.
  We say that $t$ is _closed_ if $Var(t) = emptyset$.
]
#def[$Var(phi)$][
  Let $phi$ be an atomic $cal(L)$-formula. Then, the _set of variables of $phi$_, again denoted $Var(phi)$ is defined as follows:
  + If $phi$ is of the form $t_1 eq^. t_2$ for $cal(L)$-terms $t_1, t_2$ then $Var(phi) = Var(t_1) union Var(t_2)$.
  + If $phi$ is of the form $underline(R)(t_1, ..., t_n)$ for some $n$-ary relation symbol $underline(R) in Rel(cal(L))$ and $cal(L)$-terms $t_1, ..., t_n$, then $Var(phi) = union.big_(i <= n) Var(t_i)$.
]
#def[$Var(phi), Free(phi), Bound(phi)$][
  Let $cal(L)$ be a first-order formula and $phi$ an $cal(L)$-formula. We define three things at the same time:
  + The _variables_ of $phi$ denoted $Var(phi)$.
  + The _free_ variables of $phi$, denoted $Free(phi)$.
  + The _bound_ variables of $phi$, denoted $Bound(phi)$.
  By indction on the structure of $phi$, as follows:
  + If $phi$ is atomic, then $Free(phi) = Var(phi), Bound(phi) = emptyset$.
  + Suppose we have defined our three sets for the $cal(L)$-formulas $phi_1$ and $phi_2$.
    - $
        Var(phi_1 and phi_2) = Var(phi_1) union Var(phi_2), \
        Free(phi_1 and phi_2) = Free(phi_1) union Free(phi_2), \
        Bound(phi_1 and phi_2) = Bound(phi_1) union Bound(phi_2), \
      $
    - $
        Var(phi_1 or phi_2) = Var(phi_1) union Var(phi_2), \
        Free(phi_1 or phi_2) = Free(phi_1) union Free(phi_2), \
        Bound(phi_1 or phi_2) = Bound(phi_1) union Bound(phi_2), \
      $
    - $
        Var(phi_1 -> phi_2) = Var(phi_1) union Var(phi_2), \
        Free(phi_1 -> phi_2) = Free(phi_1) union Free(phi_2), \
        Bound(phi_1 -> phi_2) = Bound(phi_1) union Bound(phi_2), \
      $
    - $
        Var(not phi_1) = Var(phi_1) \
        Free(not phi_1) = Free(phi_1) \
        Bound(not phi_1) = Bound(phi_1) \
      $
    - And now we come to the heart of the cheese, $Var((forall x) phi) = Var(phi)$, but:
      $
        Free((forall x) phi) = Free(phi) \\ {x}.
      $
      and
      $
        Bound((forall x) phi) = cases(
          Bound(phi) union {x} &"   if" x in Free(phi),
          Bound(phi) &"   if" x in.not Free(phi),
        )
      $
    - $Var((exists x) phi), Free((exists x) phi)$, and $Bound((exists x) phi)$ are defined analogously. \
  We call an $cal(L)$-formula $phi$ an $cal(L)$-sentence if $Free(phi) = nothing$.
]
#def[Vacuous][
  Let $cal(L)$ be a first-order language and $phi$ an $cal(L)$-formula. If $phi$ is of the form $(forall x)psi$ (respectively $(exists x)psi$) and $x in.not Bound(phi)$ (i.e. $x in.not Free(psi)$), then we say that the quantifier $(forall x)$ (resp. $(exists x)$) is _vacuous_ in $phi$.
]
#def[Substitution for $underline(f) in Fun(cal(L))$][
  Let $cal(L)$ be a first-order language, $t$ an $cal(L)$-term and $x, y in Var$. We define the term $t[y\/x]$ inductively, as follows:
  + If $t$ is the variable $x$ then $t[y\/x]$ is the variable $y$.
  + If $t$ is a constant symbol, then $t[y\/x]$ is just $t$.
  + If $t$ is of the form $underline(f)(t_1, ..., t_n)$ for some $n$-ary function symbol $underline(f) in Fun(cal(L))$ and $cal(L)$-terms $t_1, ..., t_n$, then $t[t\/x]$ is the term $underline(f)(t_1 [y\/x], ..., t_n [y\/x])$.
]
#def[Subtitution for $underline(R) in Rel(cal(L))$][
  Let $cal(L)$ be a first-order language, $phi$ an atomic $cal(L)$-formula and $x, y in Var$. Then, the atomic formula $phi[y\/x]$ is defined inductively as follows:
  + If $phi$ is of the form $t_1 eq^. t_2$ for $cal(L)$-terms $t_1, t_2$ then $phi[y\/x]$ is the formula $t_1 [y\/x] =^. t_2 [y\/x]$.
  + If $phi$ is of the form $underline(R) (t_1, ..., t_n)$ for some $n$-ary relation symbol $underline(R) in Rel(cal(L))$ and $cal(L)$-terms $t_1, ..., t_n$, then $phi[y\/x]$ is the formula $underline(R)(t_1 [y\/x], ..., t_n [y\/x])$.
  We now have the fools to define a notion of _free-variable_ substitution. The definition is somewhat complicated.
]
#def[Free-variable substitution][
  Let $cal(L)$ be a first-order language, $phi$ an $cal(L)$-formula and $x, y in Var$. We define $phi[y\/x]_"free"$ inductively, as follows:
  + If $phi$ is atomic, then $phi[y\/x]_"free"$ is just the atomic formula $phi[y\/x]$ defined above.
  + Suppose we have defined $phi_1 [y\/x]_"free"$ and $phi_2 [y\/x]_"free"$. Then:
    - $(phi_1 and phi_2)[y\/x]_"free"$ is the formula $(phi_1 [y\/x]_"free" and phi_2 [y\/x]_"free")$.
    - $(phi_1 or phi_2)[y\/x]_"free"$ is the formula $(phi_1 [y\/x]_"free" or phi_2 [y\/x]_"free")$.
    - $(phi_1 -> phi_2)[y\/x]_"free"$ is the formula $(phi_1 [y\/x]_"free" -> phi_2 [y\/x]_"free")$.
    - $(not phi_1)[y\/x]_"free"$ is the formula $(not phi_1 [y\/x]_"free")$.
    - $(forall z) phi [y\/x]_"free"$ is defined as follows:
      $
        (forall z) phi[y\/x]_"free" := cases(
          (forall x)phi &"   if" z = x,
          (forall z)(phi[y\/x]_"free") &"   otherwise"
        )
      $
    - $(exists z) phi [y\/x]_"free"$ is similarly defined as follows:
      $
        (exists z) phi[y\/x]_"free" := cases(
          (exists x)phi &"   if" z = x,
          (exists z)(phi[y\/x]_"free") &"   otherwise"
        )
      $
]
#def[Clean][
  We say that an $cal(L)$-formula $phi$ is _clean_ if:
  + $Bound(phi) inter Free(phi) = nothing$
  + For any $x in Var$, if $phi$ has a subformula of the form $(forall x)psi$ or $(exists x) psi$, then $x in.not Bound(psi)$
]
#exercise(num: "2.1/2.1.1")[
  *2.1. Axioms for Equality*. We need to make sure that our proof system understands that the symbol $eq^.$ behaves like equality. The best (and only) way to do this is to hardcode it:
  - (E1) Reflexivity: $(forall x)(x eq^. x)$.
  - (E2) Symmetry: $(forall x)(forall y)(x eq^. y -> y eq^. x)$.
  - (E3) Transitivity: $(forall x)(forall y)(forall z)(x eq^. y and y eq^. z -> x eq^. z)$.
  - (E4) For each $n$-ary relation symbol $underline(R) in sans("Rel")(cal(L))$ a "congruence" axiom:
    $
      (forall x_1) ... (forall x_n) (forall y_1) .. (forall y_n) (and.big x_i = y_i -> (underline(R)(x_1, ..., x_n) -> underline(R)(y_1, ..., y_n))).
    $
  - (E5) For each $n$-ary function symbol $underline(f) in sans("Fun")(cal(L))$ a "congruence" axiom:
    $
      (forall x_1) ... (forall x_n) (forall y_1) .. (forall y_n) (and.big x_i = y_i -> (underline(f)(x_1, ..., x_n) eq^. underline(R)(y_1, ..., y_n))).
    $
  *Exercise 2.1.1*: Show that (E1)-(E5) are tautologies.
]
#exercise(num: "2.2/2.2.1")[
  *2.2 Quantifier Axioms*. We also need some axioms that tell our proof system what the deal with quantifier is. We'll be somewhat economical here:
  - (Q1) For every $cal(L)$-formula $phi$ such that $x in.not sans("Free")(phi)$ and every $cal(L)$-formula $psi$, the axiom:
    $
      (forall x)(phi -> psi) -> (phi -> (forall x)psi).
    $
  - (Q2) For every $cal(L)$-formula $phi$ and every $cal(L)$-term $t$ the axiom:
    $
      (forall x)phi -> phi [t \/ x].
    $
  - (Q3) For every $cal(L)$-formula $phi$ and every $cal(L)$-term $t$ the axiom:
    $
      phi[t\/x] -> (exists x) phi
    $
]
#remark(num: "2.3/2.3.1")[
  Recall our three axioms from back in the day, but now where we allow $phi, psi, "and" chi$ to be arbitrary $cal(L)$-formulas:
  - (A1) $(phi -> (psi -> phi))$
  - (A2) $((phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> psi)))$
  - (A3) $((not phi -> not psi) -> ((not phi -> psi) -> phi))$
  Since these are subtitutions into propositional tautologies, we have the following, right away:

  *All instances of (A1) - (A3) are universally valid*.
]
#thm(num: "3.2.1")[ (Soundness) \
  Let $T$ be an $cal(L)$-theory, and $phi$ be an $cal(L)$-sentence. If $T ded(L) phi$, then $T models phi$.
]
#proof[
  Combine _Exercises 2.1.1_ and _2.2.1_ and _Remark 2.3.1_. Then prove that:
  - If $T models phi$ and $T models phi -> psi$ then $T models psi$.
  - If $T models phi$ then $T models (forall x) phi$.
]
