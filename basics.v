From Stdlib Require Import List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

Record Language : Type := {
    (* Constants are f in Funcs where arityF f = 0 *)
    Functions : Type;
    Relations : Type;
    arityF : Functions -> nat;
    arityR : Relations -> nat;
}.

Definition Var := nat.

(* raw term, naive- no arity checking *)
Inductive Term (L : Language) : Type :=
  | var  : Var -> Term L
  | func : Functions L -> list (Term L) -> Term L.

Arguments var  {L} _.
Arguments func {L} _ _.

(* well-formed term *)
Inductive wf_term (L : Language) : Term L -> Prop :=
| wf_var  : forall x, wf_term L (var x)
| wf_func : forall f ts,
      (* arity matches list length *)
      length ts = (arityF L) f ->
      (* all t are L-terms *)
      Forall (wf_term L) ts ->
      (* f(t_1, ..., t_s) is well-formed *)
      wf_term L (func f ts).

(* every L-term is finitely generated *)
Lemma term_in_n_steps:
  forall (L : Language) (t : Term L),
    wf_term L t -> exists n : nat, True.
Proof.
  intros L t H.
  induction H.
  - (* var *)
    exists 0. trivial.
  - (* func *)
    induction H0; exists 0; trivial.
Qed.


(* atomic L-Formulas, not conerning arity *)
Inductive Atom (L : Language) : Type :=
(* given t_1, t_2 L-terms, eq_atom t_1 t_2 is atomic *)
| eq_atom  : Term L -> Term L -> Atom L
(* rel with list of ts, is atomic *)
| rel_atom : forall (R : Relations L), list (Term L) -> Atom L.

Arguments eq_atom {L} _ _.
Arguments rel_atom {L} _ _.

(* atomic concerning arity, i.e. well-formed *)
Inductive wf_atom (L : Language) : Atom L -> Prop :=
| wf_eq : forall t1 t2,
      wf_term L t1 ->
      wf_term L t2 ->
      wf_atom L (eq_atom t1 t2)
| wf_rel : forall (R : Relations L) (ts : list (Term L)),
      length ts = (arityR L R) ->
      Forall (wf_term L) ts ->
      wf_atom L (rel_atom R ts).

Inductive Formula (L : Language) : Type :=
| Fatom   : Atom L -> Formula L
| Fand    : Formula L -> Formula L -> Formula L
| For     : Formula L -> Formula L -> Formula L
| Fimpl   : Formula L -> Formula L -> Formula L
| Fnot    : Formula L -> Formula L
| Fforall : nat -> Formula L -> Formula L
| Fexists : nat -> Formula L -> Formula L.

Arguments Fatom   {L} _.
Arguments Fand    {L} _ _.
Arguments For     {L} _ _.
Arguments Fimpl   {L} _ _.
Arguments Fnot    {L} _.
Arguments Fforall {L} _ _.
Arguments Fexists {L} _ _.

Inductive wf_formula (L : Language) : Formula L -> Prop :=
| wf_Fatom : forall a,
    wf_atom L a ->
    wf_formula L (Fatom a)
| wf_Fand : forall phi psi,
    wf_formula L phi ->
    wf_formula L psi ->
    wf_formula L (Fand phi psi)
| wf_For : forall phi psi,
    wf_formula L phi ->
    wf_formula L psi ->
    wf_formula L (For phi psi)
| wf_Fimpl : forall phi psi,
    wf_formula L phi ->
    wf_formula L psi ->
    wf_formula L (Fimpl phi psi)
| wf_Fnot : forall phi,
    wf_formula L phi ->
    wf_formula L (Fnot phi)
| wf_Fforall : forall x phi,
    wf_formula L phi ->
    wf_formula L (Fforall x phi)
| wf_Fexists : forall x phi,
    wf_formula L phi ->
    wf_formula L (Fexists x phi).

Fixpoint vars_term {L : Language} (t : Term L) : list nat :=
  match t with
  | var x => [x]
  | func f ts => concat (map vars_term ts)
  end
.

Definition closed_term {L : Language} (t : Term L) : Prop := vars_term t = [].

Definition vars_atom {L : Language} (a : Atom L) : list nat :=
  match a with
  | eq_atom t1 t2 => vars_term t1 ++ vars_term t2
  | rel_atom _ ts => concat (map vars_term ts)
  end
.

Fixpoint vars_formula (L : Language) (phi : Formula L) : list nat :=
  match phi with
  | Fatom a         => vars_atom a
  | Fand phi1 phi2  => vars_formula L phi1 ++ vars_formula L phi2
  | For phi1 phi2   => vars_formula L phi1 ++ vars_formula L phi2
  | Fimpl phi1 phi2 => vars_formula L phi1 ++ vars_formula L phi2
  | Fnot phi1       => vars_formula L phi1
  | Fforall x phi1  => vars_formula L phi1
  | Fexists x phi1  => vars_formula L phi1
  end
.

Fixpoint free_vars (L : Language) (phi : Formula L) : list nat :=
  match phi with
  | Fatom a         => vars_atom a
  | Fand phi1 phi2  => free_vars L phi1 ++ free_vars L phi2
  | For phi1 phi2   => free_vars L phi1 ++ free_vars L phi2
  | Fimpl phi1 phi2 => free_vars L phi1 ++ free_vars L phi2
  | Fnot phi1       => free_vars L phi1
  | Fforall x phi1  => remove Nat.eq_dec x (free_vars L phi1)
  | Fexists x phi1  => remove Nat.eq_dec x (free_vars L phi1)
  end
.

Fixpoint bound_vars (L : Language) (phi : Formula L) : list nat :=
  match phi with
  | Fatom _         => []
  | Fand phi1 phi2  => bound_vars L phi1 ++ bound_vars L phi2
  | For phi1 phi2   => bound_vars L phi1 ++ bound_vars L phi2
  | Fimpl phi1 phi2 => bound_vars L phi1 ++ bound_vars L phi2
  | Fnot phi1       => bound_vars L phi1
  | Fforall x phi1  =>
      if existsb (Nat.eqb x) (free_vars L phi1)
      then x :: bound_vars L phi1
      else bound_vars L phi1
  | Fexists x phi1  =>
      if existsb (Nat.eqb x) (free_vars L phi1)
      then x :: bound_vars L phi1
      else bound_vars L phi1
  end
.

Definition vars_term_set    (L : Language) (t : Term L) : list nat := nodup Nat.eq_dec (vars_term t).
Definition vars_atom_set    (L : Language) (a : Atom L) : list nat := nodup Nat.eq_dec (vars_atom a).
Definition vars_form_set    (L : Language) (f : Formula L) : list nat := nodup Nat.eq_dec (vars_formula L f).

Definition vars_formula_set (L : Language) (phi : Formula L) := nodup Nat.eq_dec (vars_formula L phi).
Definition free_vars_set    (L : Language) (phi : Formula L) := nodup Nat.eq_dec (free_vars L phi).
Definition bound_vars_set   (L : Language) (phi : Formula L) := nodup Nat.eq_dec (bound_vars L phi).

Definition sentence (L : Language) (phi : Formula L) : Prop := free_vars L phi = [].

Definition vacuous_forall (L : Language) (x : nat) (phi : Formula L) : Prop :=
  match phi with
  | Fforall y psi => y = x /\ ~ In x (free_vars L psi)
  | _ => False
  end
.

Definition vacuous_exists (L : Language) (x : nat) (phi : Formula L) : Prop :=
  match phi with
  | Fexists y psi => y = x /\ ~ In x (free_vars L psi)
  | _ => False
  end
.

Section VacuumEx.
Definition L : Language :=
  {| Functions := unit;
     Relations := unit;
     arityF := fun _ => 0;
     arityR := fun _ => 2 |}.
Example test_vacuum :
  let phi := Fforall 1 (Fatom (eq_atom (var 2) (var 3))) in vacuous_forall L 1 phi.
Proof.
  unfold vacuous_forall.
  simpl.
  split; auto.
  intro H. inversion H. discriminate. Abort.
End VacuumEx.

Fixpoint subst_term {L : Language} (t : Term L) (x y : nat) : Term L :=
  match t with
  | var z => if Nat.eq_dec z x then var y else var z
  | func f ts => func f (map (fun t' => subst_term t' x y) ts)
  end
.

Definition subst_atom {L : Language} (phi : Atom L) (x y : nat) : Atom L :=
  match phi with
  | eq_atom t1 t2 => eq_atom (subst_term t1 x y) (subst_term t2 x y)
  | rel_atom R ts => rel_atom R (map (fun t => subst_term t x y) ts)
  end
.

Fixpoint subst_formula_free {L : Language} (phi : Formula L) (x y : nat) : Formula L :=
  match phi with
  | Fatom a =>
      Fatom (subst_atom a x y)
  | Fand phi1 phi2 =>
      Fand (subst_formula_free phi1 x y) (subst_formula_free phi2 x y)
  | For phi1 phi2 =>
      For (subst_formula_free phi1 x y) (subst_formula_free phi2 x y)
  | Fimpl phi1 phi2 =>
      Fimpl (subst_formula_free phi1 x y) (subst_formula_free phi2 x y)
  | Fnot phi1 =>
      Fnot (subst_formula_free phi1 x y)
  | Fforall z phi1 =>
      if Nat.eq_dec z x
      then Fforall z phi1
      else Fforall z (subst_formula_free phi1 x y)
  | Fexists z phi1 =>
      if Nat.eq_dec z x
      then Fexists z phi1
      else Fexists z (subst_formula_free phi1 x y)
  end
.

Definition disjoint {A : Type} (l1 l2 : list A) : Prop :=
  forall x, In x l1 -> ~ In x l2.

(*Fixpoint subformula {L : Language} (phi psi : Formula L) : Prop :=*)
(*  phi = psi \/*)
(*  match phi with*)
(*  | Fatom _ => False*)
(*  | Fand phi1 phi2*)
(*  | For phi1 phi2*)
(*  | Fimpl phi1 phi2 => subformula phi1 psi \/ subformula phi2 psi*)
(*  | Fnot phi1       => subformula phi1 psi*)
(*  | Fforall _ phi1*)
(*  | Fexists _ phi1  => subformula phi1 psi*)
(*  end*)
(*.*)

Fixpoint clean_formula_rec (L : Language) (phi : Formula L) : Prop :=
  disjoint (bound_vars L phi) (free_vars L phi) /\
  match phi with
  | Fatom _ => True
  | Fand phi1 phi2
  | For phi1 phi2
  | Fimpl phi1 phi2 => clean_formula_rec L phi1 /\ clean_formula_rec L phi2
  | Fnot phi1       => clean_formula_rec L phi1
  | Fforall x phi1  => ~ In x (bound_vars L phi1) /\ clean_formula_rec L phi1
  | Fexists x phi1  => ~ In x (bound_vars L phi1) /\ clean_formula_rec L phi1
  end.

Definition clean_formula (L : Language) (phi : Formula L) : Prop := clean_formula_rec L phi.

Example phi_clean_example : clean_formula L (Fforall 1 (Fatom (eq_atom (var 2) (var 3)))).
Proof.
  simpl. split.
  - intros x H. inversion H.
  - split; compute; auto.
Qed.

(*Arguments Formula {L}.*)
(*Arguments wf_formula {L} _.*)

Record Structure (L : Language) : Type := {
  domain : Type;
  (* remember, constants are functions with 0 arity *)
  interp_fun : forall (f : Functions L),
    list domain -> domain;
  interp_rel : forall (R : Relations L),
    list domain -> Prop
}.

Definition Assignment {L : Language} (M : Structure L) : Type := nat -> domain L M.

(*
See week 3b of Aris' notes for reference on def of Languages
1. Logical Symbols (countable variables, all logical symbols, equality)
2. Language \mathcal{L} (constants, function symbols, relation symbols, arity)
*)
(**)
(*Section LanguageDef.*)
(**)
(*(* This is the \mathcal{L} we use for standard definitions, *)
(*eg for \mathcal{L}-structures *)*)
(*Variable L: Language.*)
(**)
(*Definition LFunctions := Functions L.*)
(*Definition LRelations := Relations L.*)
(*Definition LarityF := arityF L.*)
(*Definition LarityR := arityR L.*)
(*Definition Larity (s: LRelations + LFunctions) : nat :=*)
(*  match s with*)
(*  | inl r => LarityR r*)
(*  | inr f => LarityF f*)
(*  end.*)
(**)
(**)
(*(* The idea here is that we define terms as either variables or function applications. *)*)
(*Inductive Term: Set := *)
(*  | var: nat -> Term*)
(*  | func: forall (f: LFunctions), Terms (LarityF f) -> Term*)
(*with Terms: nat -> Set := *)
(*  | Term_Nil: Terms 0*)
(*  | Term_Cons: forall (n: nat), Term -> Terms n -> Terms (S n).*)
(**)
(*(**)
(*Trouble: This definition now holds on arity, and arity is not necessarily positive if defined entirely separately.*)
(**)*)
(**)
(*(* Define lists of terms *)*)
(*(**)
(*Type is nat -> Set, where the nat indicates the length of the list.*)
(**)*)
(**)
(*(**)
(*Formulas are either atomic formulas (relation applications) or built up from*)
(*other formulas using logical connectives and quantifiers.*)
(**)*)
(**)
(*Inductive Formula: Set := *)
(*  | atomic: forall (r: LRelations), Terms (LarityR r) -> Formula*)
(*  | equal: Term -> Term -> Formula (* equality defined as a relation. If a term equals a nother term, we are given the atomic forula t1 \doteq t2. Aris' notes uses doteq but we will use eq here for the sake of brevity and because we will not introduce another equality *)*)
(*  | notH: Formula -> Formula (* We can construct all other logical connectives from not, implies, and forall *)*)
(*  | impH: Formula -> Formula -> Formula*)
(*  | allH: nat -> Formula -> Formula*)
(*.*)
(**)
(*Fixpoint depth (A : Formula) : nat :=*)
(*  match A with*)
(*  | atomic r terms => 0*)
(*  | equal t1 t2 => 0*)
(*  | notH f => S (depth f)*)
(*  | impH f1 f2 => S (Nat.max (depth f1) (depth f2))*)
(*  | allH v f => S (depth f)*)
(*  end.*)
(**)
(*Definition depth_lt (A : Formula) (B: Formula) : Prop :=*)
(*  depth A < depth B.*)
(*Definition depth_le (A : Formula) (B: Formula) : Prop :=*)
(*  depth A <= depth B.*)
(*Definition depth_eq (A : Formula) (B: Formula) : Prop :=*)
(*  depth A = depth B.*)
(*Definition depth_ge (A : Formula) (B: Formula) : Prop :=*)
(*  depth A >= depth B.*)
(*Definition depth_gt (A : Formula) (B: Formula) : Prop :=*)
(*  depth A > depth B.*)
(*(* Some convenient notations *)*)
(**)
(*Definition LFormula := Formula.*)
(*Definition LTerm := Term.*)
(*Definition LTerms := Terms.*)
(*Definition Formulas := list Formula.*)
(**)
(*(* Todo: define schema for recursion, induction, then for other logical connectives, nil terms, prove decideability of things, etc. *)*)
(**)
(*(**)
(*Verify these with truthtables if you so wish*)
(**)*)
(*Definition orH (A B: Formula) := impH (notH A) B.*)
(*Definition andH (A B: Formula) := notH (orH (notH A) (notH B)).*)
(*Definition iffH (A B: Formula) := *)
(*  andH (impH A B) (impH B A).*)
(*Definition existsH (v: nat) (f: Formula) :=*)
(*  notH (allH v (notH f)).*)
(**)
(*(* some fixpoints and lemmas *)*)
(*Fixpoint accum_list (l : list Term) : nat :=*)
(*  match l with*)
(*  | nil => 0*)
(*  | cons t ts => 1 + (accum_list ts)*)
(*  end.*)
(**)
(*Definition language_decideable := *)
(*((forall t1 t2 : Functions L, {t1 = t2} + {t1 <> t2}) **)
(* (forall t1 t2 : Relations L, {t1 = t2} + {t1 <> t2}))%type.*)
(* (*(forall t1 t2 : Constants L, {t1 = t2} + {t1 <> t2}))%type.*)*)
(**)
(*Let nil_terms : Terms 0 := Term_Nil.*)
(**)
(*(* some test lemmas *)*)
(*Lemma depthNot : *)
(*  forall A: Formula, depth_lt A (notH A).*)
(*Proof. unfold depth_lt. intros A. simpl. auto. Qed.*)
(**)
(*Lemma nil_terms_unique:*)
(*  forall n: nat, n=0 -> Terms n.*)
(*Proof.*)
(*  intros n H. rewrite H. apply nil_terms.*)
(*Qed.*)
(**)
(*(* semantics? *)*)
(*End LanguageDef.*)
(**)
(*Section Semantics.*)
(**)
(*(**)
(*A structure for a language L consists of a non-empty set M (the domain),*)
(*an interpretation of each constant symbol as an element of M, etc*)
(**)*)
(*Variable L : Language.*)
(**)
(*Record Structure : Type := {*)
(*  M: Type;*)
(*  M_NE: inhabited M;*)
(*  (*interpC: Constants L -> M;*)*)
(*  interpR: forall R : LRelations L, list M -> Prop;*)
(*  interpF: forall f : LFunctions L, list M -> M;*)
(*}.*)
(**)
(*(* nat comes from var def *)*)
(*Definition assignment (S : Structure) : Type := nat -> M S.*)
(**)
(*Variable S : Structure.*)
(**)
(*End Semantics.*)
(**)
