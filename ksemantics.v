From FOL Require Import basics.
From Stdlib Require Import Peano_dec EqNat.
From FOL Require Import overloadedbullshit.
From Stdlib Require Import List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope type_scope.
(*
This section is unabashedly stolen from the Coq formalization of the
Kripke semantics of linear logic (by Mamane, Geuvers, and McKinna)

, with modifications to fit our
semantics
*)
Section Concrete_Semantics.

Definition Kworld : Set := cxt_trm * cxt_ect.
  
  Definition Kle (w w':Kworld) : Type :=
    (incl (fst w) (fst w')) * (incl (snd w) (snd w')).
  
  Lemma Kle_refl : forall w, Kle w w.
  Proof.
    intro w.
    split;
      auto using incl_refl.
  Defined.
  
  Lemma Kle_trans : forall w w' w'', Kle w w' -> Kle w' w'' -> Kle w w''.
  Proof.
    unfold Kle.
    intros.
    intuition eauto using incl_tran.
  Defined.

  Definition Kexploding (w:Kworld) : Set := 
    {c:command & proof_cmd c (fst w) (snd w)}.
  Hint Unfold Kexploding.

  Definition Normal_trm (A:typ)(Gamma:cxt_trm)(Delta:cxt_ect) :=
    sigT (fun t:term => proof_trm Gamma t A Delta).
  Hint Unfold Normal_trm.

  Definition Normal_ect (A:typ)(Gamma:cxt_trm)(Delta:cxt_ect) :=
    sigT (fun e:ect => proof_ect Gamma e A Delta).
  Hint Unfold Normal_ect.

  Definition Kaforces (w:Kworld)(p:predicate)(ld:list indiv) : Set := 
    Normal_trm (@Atom p ld) (fst w) (snd w).
  Hint Unfold Kaforces.

  Lemma proof_weaken : 
    (forall c Gamma Delta, c:(Gamma|-Delta) -> 
      forall Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
        c:(Gamma'|-Delta')) *
    (forall Gamma t A Delta, Gamma|-(t:A);Delta -> 
      forall Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
        Gamma'|-(t:A);Delta') *
    (forall Gamma e A Delta, Gamma;(e:A)|-Delta ->
      forall Gamma' Delta', incl Gamma Gamma' -> incl Delta Delta' ->
        Gamma';(e:A)|-Delta').
  Proof.
    apply proof_rect'.

    (* Cut *)
    eauto using Cut.

    (* AxR *)
    eauto using AxR.
  Admitted.

  Lemma Kaforces_mon : forall w P ld, @Kaforces w P ld ->
    forall w', Kle w w' -> @Kaforces w' P ld.
  Proof.
    intros w P ld H.
    destruct H as [v p].
    intros w' Hle.
    exists v.
    unfold Kle in Hle.
    destruct Hle.
    apply (snd (fst proof_weaken)) with (fst w) (snd w); auto.
  Defined.

  Definition K : Kripke.
  (* begin show *)
    apply Build_Kripke with Kworld Kle Kaforces.
    exact Kle_refl.
    exact Kle_trans.
    exact Kexploding.
    exact Kaforces_mon.
  (* end show *)
  Defined.
End Concrete_Semantics.