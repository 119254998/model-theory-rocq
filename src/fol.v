From Stdlib Require Import List.

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
  | func: forall (f: LFunctions), Terms (LarityF f) -> Term
with Terms: nat -> Set := 
  | Term_Nil: Terms 0
  | Term_Cons: forall (n: nat), Term -> Terms n -> Terms (S n).
(* Define lists of terms *)
(*
Type is nat -> Set, where the nat indicates the length of the list.
*)

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

Fixpoint depth (A : Formula) : nat :=
  match A with
  | atomic r terms => 0
  | equal t1 t2 => 0
  | notH f => S (depth f)
  | impH f1 f2 => S (Nat.max (depth f1) (depth f2))
  | allH v f => S (depth f)
  end.

Definition depth_lt (A : Formula) (B: Formula) : Prop :=
  depth A < depth B.
Definition depth_le (A : Formula) (B: Formula) : Prop :=
  depth A <= depth B.
Definition depth_eq (A : Formula) (B: Formula) : Prop :=
  depth A = depth B.
Definition depth_ge (A : Formula) (B: Formula) : Prop :=
  depth A >= depth B.
Definition depth_gt (A : Formula) (B: Formula) : Prop :=
  depth A > depth B.
(* Some convenient notations *)

Definition LFormula := Formula.
Definition LTerm := Term.
Definition LTerms := Terms.
Definition Formulas := list Formula.

(* Todo: define schema for recursion, induction, then for other logical connectives, nil terms, prove decideability of things, etc. *)

(*
Verify these with truthtables if you so wish
*)
Definition orH (A B: Formula) := impH (notH A) B.
Definition andH (A B: Formula) := notH (orH (notH A) (notH B)).
Definition iffH (A B: Formula) := 
  andH (impH A B) (impH B A).
Definition existsH (v: nat) (f: Formula) :=
  notH (allH v (notH f)).

(* some fixpoints and lemmas *)
Fixpoint accum_list (l : list Term) : nat :=
  match l with
  | nil => 0
  | cons t ts => 1 + (accum_list ts)
  end.

Definition language_decideable := 
((forall t1 t2 : Functions L, {t1 = t2} + {t1 <> t2}) *
 (forall t1 t2 : Relations L, {t1 = t2} + {t1 <> t2}) *
 (forall t1 t2 : Constants L, {t1 = t2} + {t1 <> t2}))%type.

Let nil_terms : Terms 0 := Term_Nil.

(* some test lemmas *)
Lemma depthNot : 
  forall A: Formula, depth_lt A (notH A).
Proof. unfold depth_lt. intros A. simpl. auto. Qed.

Lemma nil_terms_unique:
  forall n: nat, n=0 -> Terms n.
Proof.
  intros n H. rewrite H. apply nil_terms.
Qed.


(* 1) uniqueness for Terms 0 *)
Lemma Terms0_unique : forall (t : Terms 0), t = Term_Nil.
Proof.
  intros t.
Admitted.

(* 2) decomposition for Terms (S n) *)
Lemma cons_terms :
  forall (n : nat) (x : Terms (S n)),
    exists (hd : Term) (tl : Terms n), x = Term_Cons n hd tl.
Proof.
  intros n x.
  destruct x as [| n' hd tl].
    discriminate.
  - exists hd, tl.
    reflexivity.
Qed.

(* 3) decidability of Term equality *)
Lemma term_dec : forall (x y : Term), {x = y} + {x <> y}.
Proof.
  intros x y.
  destruct language_decideable as [Hf [Hr Hc]].
  decide equality.
  - apply eq_nat_dec.
  - apply Hf.
  - apply eq_nat_dec.
Qed.
End LanguageDef.

(* semantics? *)

Section Semantics.

(*
A structure for a language L consists of a non-empty set M (the domain),
an interpretation of each constant symbol as an element of M, etc
*)
Variable L : Language.
Record Structure : Type := {
  M: Type;
  M_NE: inhabited M;
  interpC: Constants L -> M;
  interpR: forall R : LRelations L, list M -> Prop;
  interpF: forall f : LFunctions L, list M -> M;
}.

(* nat comes from var def *)
Definition assignment (S : Structure) : Type := nat -> M S.

Variable S : Structure.

End Semantics.

