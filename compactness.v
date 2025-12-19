From FOL Require Import overloadedbullshit basics ksemantics completeness.
From Stdlib Require Import Peano_dec EqNat.
From Stdlib Require Import List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope type_scope.

Notation "w  <=  w'" := (Kle w w').

Notation "w : ||+ A " := (@sforces K w A) (at level 70).
Notation "w : A ||- " := (@refutes K w A)  (at level 70).
Notation "w : ||- A " := (Kont (@sforces K) w A) (at level 70).
Notation " w : ||-- Gamma " := (@forces_cxt K w Gamma) (at level 70).
Notation " w : Delta ||-- "  := (@refutes_cxt K w Delta) (at level 70).
(*
Now that we have completeness and soundness compactness just follows very quickly
*)
Fixpoint locl_cxt_trm (Gamma:cxt_trm) : Prop :=
  match Gamma with
    | nil => True
    | cons a Gamma' => locl (snd a) /\ locl_cxt_trm Gamma'
  end.

Fixpoint locl_cxt_ect (Delta:cxt_ect) : Prop :=
  match Delta with
    | nil => True
    | cons a Delta' => locl (snd a) /\ locl_cxt_ect Delta'
  end.

Parameter tf : var_term.
Parameter ef : var_ect.

(*
When forcing, they are identical
*)
Lemma forces_cxt_id : forall Gamma Delta, locl_cxt_trm Gamma -> locl_cxt_ect Delta -> @forces_cxt K (Gamma,Delta) Gamma.
Proof.
  induction Gamma.
  simpl. constructor. simpl. intros Delta [Hlocl HloclGamma] HloclDelta. split. set (w0 := (a :: Gamma, Delta)). intros w1 w0w1 Ha. simpl in w0w1. change (w0 <= w1) in w0w1. change (w1:snd a||-) in Ha.  simpl. 
  apply (snd (@Completeness (depth (snd a)) (snd a) (le_n _) Hlocl w1 tf ef)) in Ha.
  destruct Ha as [e pe]. exists (cm (t_var (fst a)) e). apply Cut with (snd a). apply AxR. apply w0w1. simpl. left. destruct a;auto.
  assumption.
  apply forces_cxt_mon with (Gamma, Delta).
  auto. simpl. unfold Kle. unfold incl. simpl. auto.
Qed.

Lemma refutes_cxt_id : forall Gamma Delta, locl_cxt_trm Gamma -> locl_cxt_ect Delta -> @refutes_cxt K (Gamma,Delta) Delta.
Proof.
  induction Delta. simpl. constructor. simpl. intros HloclGamma [Hlocl HloclDelta]. split. set (w0 := (Gamma, a::Delta)). intros w1 w0w1 Ha. simpl in w0w1. change (w0 <= w1) in w0w1. simpl. apply ret in Ha.
  apply (fst (@Completeness (depth (snd a)) (snd a) (le_n _) Hlocl w1 tf ef)) in Ha.
  destruct Ha as [t pt]. exists (cm t (e_var (fst a))). apply Cut with (snd a). assumption. apply AxL. apply w0w1. simpl.
  left.
  destruct a;auto.
  apply refutes_cxt_mon with (Gamma, Delta).
  auto. simpl. unfold Kle. unfold incl. simpl. auto.
Qed.

Definition Compactness : forall c Gamma Delta, 
  locl_cxt_trm Gamma -> locl_cxt_ect Delta -> proof_cmd c Gamma Delta ->
  sigT (fun (c':command) => proof_cmd c' Gamma Delta).
Proof.
  intros c Gamma Delta HloclGamma HloclDelta H.
  destruct c as [t e]. inversion H. clear -H2 H5 HloclGamma HloclDelta.
  assert (HGamma : @forces_cxt K (Gamma,Delta) Gamma).
    apply forces_cxt_id; assumption.
  assert (HDelta : @refutes_cxt K (Gamma,Delta) Delta).
    apply refutes_cxt_id; assumption.
  assert (H2' := (snd (fst (soundness K))) Gamma t A Delta H2 (Gamma,Delta) HGamma HDelta).
  assert (H5' := (snd (soundness K)) Gamma e A Delta H5 (Gamma,Delta) HGamma HDelta).
  
  apply H2' in H5'.
  exact H5'.
  apply Kle_refl.
Qed.
