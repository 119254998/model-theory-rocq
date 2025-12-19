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

Fixpoint subformula {L : Language} (phi psi : Formula L) : Prop :=
  phi = psi \/
  match phi with
  | Fatom _ => False
  | Fand phi1 phi2
  | For phi1 phi2
  | Fimpl phi1 phi2 => subformula phi1 psi \/ subformula phi2 psi
  | Fnot phi1       => subformula phi1 psi
  | Fforall _ phi1
  | Fexists _ phi1  => subformula phi1 psi
  end
.

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
