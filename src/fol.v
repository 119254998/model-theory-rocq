Require Import List.

(* We aim to define the fundamentals of first order logic *)

Record Language : Type := {
    Constants: Set;
    Functions: Set;
    Relations: Set; 
    arityF: Functions -> nat;
    arityR: Relations -> nat;
    arity: Relations + Functions -> nat
}.

(*
See week 3b of Aris' notes for reference on def of Languages

1. Logical Symbols (countable variables, all logical symbols, equality)
2. Language \mathcal{L} (constants, function symbols, relation symbols, arity)
*)

Section LanguageDef.

(* This is the \mathcal{L} we use for standard definitions, 
eg for \mathcal{L}-structures *)
Variable L: Language.

Definition LFunctions := Functions L.
Definition LRelations := Relations L.
Definition LarityF := arityF L.
Definition LarityR := arityR L.
Definition Larity (s: LRelations + LFunctions) : nat :=
  match s with
  | inl r => LarityR r
  | inr f => LarityF f
  end.


(* The idea here is that we define terms as either variables or function applications. *)
Inductive Term: Set := 
  | var: nat -> Term
  | func: forall (f: LFunctions), (list Term) -> Term.

(* Define lists of terms *)
(*
Type is nat -> Set, where the nat indicates the length of the list.
*)
Inductive Terms: nat -> Set := 
  | Term_Nil: Terms 0
  | Term_Cons: forall (n: nat), Term -> Terms n -> Terms (S n).
(*
Formulas are either atomic formulas (relation applications) or built up from
other formulas using logical connectives and quantifiers.
*)

Inductive Formula: Set := 
  | atomic: forall (r: LRelations), Terms (LarityR r) -> Formula
  | equal: Term -> Term -> Formula (* equality defined as a relation. If a term equals a nother term, we are given the atomic forula t1 \doteq t2. Aris' notes uses doteq but we will use eq here for the sake of brevity and because we will not introduce another equality *)
  | notH: Formula -> Formula (* We can construct all other logical connectives from not, implies, and forall *)
  | impH: Formula -> Formula -> Formula
  | allH: nat -> Formula -> Formula
.

Definition LFormula := Formula.
Definition LTerm := Term.
Definition LTerms := Terms.
Definition Formulas := list Formula.

Fixpoint accum_list (l : list Term) : nat :=
  match l with
  | nil => 0
  | cons t ts => 1 + (accum_list ts)
  end.

Inductive In_stage : nat -> Term -> Prop :=
| Var: forall v n,
    In_stage n (var v)
| Func: forall f args n, (forall t, In t args -> In_stage n t) -> In_stage (S n) (func f args).

Lemma In_stage_mono :
  forall k n t, In_stage k t -> k <= n -> In_stage n t.
Proof.
  intros k n t IS H. induction IS.
    - constructor.
    - inversion H.
      + apply Func. assumption. 
      + apply Func. subst. apply le_S_n in H. inversion H. subst. assumption. intros t HIS. rewrite H4. apply H0 in HIS. rewrite <- H4 in H2. Admitted. 
(* Todo: define schema for recursion, induction, then for other logical connectives, nil terms, prove decideability of things, etc. *)


(*
Verify these with truthtables if you so wish
*)
Definition orH (A B: Formula) : Formula := impH (notH A) B.
Definition andH (A B: Formula) : Formula := notH (orH (notH A) (notH B)).
Definition iffH (A B: Formula) : Formula := 
  andH (impH A B) (impH B A).
Definition existsH (v: nat) (f: Formula) : Formula :=
  notH (allH v (notH f)).

(* Schema for induction on formulas *)
(* This fuckass language doesn't let me overload induction schemes 
Scheme Term_ind := Induction for Term Sort Prop. *)

(* Induction scheme for Terms and Term together *)
Scheme Term_Terms_ind := Induction for Term Sort Prop.
Scheme Terms_Term_ind := Induction for Terms Sort Prop.

Scheme Term_Terms_rec := Minimality for Term Sort Set.
Scheme Terms_Term_rec := Minimality for Terms Sort Set.

End LanguageDef.