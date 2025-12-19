(*
Holy shit, finally

I will be following a proof outline given by one of McKinna's old
papers that outlines PROPOSITIONAL completeness for a kripke
structure. This proof will be really long but
most of it is tedium now that we have a good structure
*)

From FOL Require Import overloadedbullshit basics ksemantics.
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
Define the building of a term from a command using
a binder, which in our case will be [mu] and [mut].

We start with some world, a type/formula, and a continuation
variable, and then extend the context and return a term and
most importantly a proof that t has type A in the original
context!
*)
Definition cmd_to_trm : forall w A, forall alpha:var_ect,
  let world := (fst w, (alpha,A) :: snd w) in
  sigT (fun c:command => proof_cmd c (fst world) (snd world)) ->
  sigT (fun t:term => proof_trm (fst w) t A (snd w)).
Proof.
  intros w A alpha world H.
  destruct H as [c Hc].
  exists (mu alpha c).
  constructor.
  exact Hc.
Defined.

(*
We similarly do so for evaluation contexts
*)
Definition cmd_to_ect : forall w A, forall x:var_term,
  let world := ((x,A) :: fst w, snd w) in
  sigT (fun c:command => proof_cmd c (fst world) (snd world)) ->
  sigT (fun e:ect => proof_ect (fst w) e A (snd w)).
Proof.
  intros w A x world H.
  destruct H as [c Hc].
  exists (mut x c).
  constructor.
  exact Hc.
Defined.

(*
And now, finally, we can define the building of a command from
a term and an evaluation context using a cut
*)
Definition to_cmd : forall w A,
  sigT (fun t:term => proof_trm (fst w) t A (snd w)) ->
  sigT (fun e:ect => proof_ect (fst w) e A (snd w)) ->
  sigT (fun c:command => proof_cmd c (fst w) (snd w)).
Proof.
  intros w A H1 H2.
  destruct H1 as [t Ht].
  destruct H2 as [e He].
  exists (cm t e).
  apply Cut with A.
  assumption.
  assumption.
Defined.

(*
Claim: world is related to kle by a 1 step relation. 

I have no idea how to prove this because it is kripke but I am 
assured it is true. 
*)
Lemma Kle_eta_r : forall w a, Kle w (fst w, a :: snd w).
Proof.
  intros.
  split.
  destruct w.
  simpl.
  auto.
  simpl.
  auto.
  admit.
Admitted.

Lemma Kle_eta_l : forall w a, Kle w (a :: fst w, snd w).
Proof. Admitted.

(** The proof of completeness is via a reify-reflect pair,

by induction on the complexity of the formula [A]. 

Note that because a reify–reflect pair is a pair of functions that witness an isomorphism between syntax and semantics, this IS the completeness proof.
*)
(** The proof of completeness is via a reify-reflect pair, by induction on [n] i.e. by induction on the complexity of the formula [A]. [tfresh] and [efresh] are a fresh variable counters that are increased at every recursive call. *)
Theorem Completeness : 
  forall (n:nat)(A:typ), le (depth A) n -> locl A ->
  forall (w:K)(tfresh:var_term)(efresh:var_ect),
    (w : ||- A -> Normal_trm A (fst w) (snd w)) *
    (w : A ||- -> Normal_ect A (fst w) (snd w)).
Proof.
  induction n.
  - intros A Hn.
    destruct A;inversion Hn.
  - intros A HSn Hlocl.
    intros.
    destruct A.
    + (* Atomic formulas *)
      split. 
      
      intros H. apply cmd_to_trm with efresh. apply H. simpl. apply Kle_eta_r. intros w1 w1w2. unfold sforces. simpl. intros H1. apply to_cmd with (Atom p l). exact H1. exists (e_var efresh). constructor. apply w1w2. simpl. left;reflexivity.

      intros H. apply cmd_to_ect with tfresh. apply H. apply Kle_eta_l. unfold sforces. simpl. exists (t_var tfresh). constructor. simpl. left;reflexivity.
    + (* Implication *)
      assert (Hdepth2 : le (depth A2) n).
        clear -HSn. simpl in HSn. apply le_S_n in HSn. eapply le_trans. apply le_max_r. apply HSn. 
      assert (Hdepth1 : le (depth A1) n).
        clear -HSn. simpl in HSn. apply le_S_n in HSn. eapply le_trans. apply le_max_l. apply HSn.
      assert (Hlocl1 : locl A1).
        clear -Hlocl. unfold locl in *. simpl in *. intros. assert (Hlocl' := Hlocl k d). congruence.
      assert (Hlocl2 : locl A2).
        clear -Hlocl. unfold locl in *. simpl in *. intros. assert (Hlocl' := Hlocl k d). congruence.
      split.

      intros H.
      (*
      I'm unsure how to finish this cleanly at this point
      *)
      admit.
      admit.
    + (* Disjunction *)
      assert (Hdepth2 : le (depth A2) n).
        clear -HSn. simpl in HSn. apply le_S_n in HSn. eapply le_trans. apply le_max_r. apply HSn. 
      assert (Hdepth1 : le (depth A1) n).
        clear -HSn. simpl in HSn. apply le_S_n in HSn. eapply le_trans. apply le_max_l. apply HSn.
      assert (Hlocl1 : locl A1).
        clear -Hlocl. unfold locl in *. simpl in *. intros. assert (Hlocl' := Hlocl k d). congruence.
      assert (Hlocl2 : locl A2).
        clear -Hlocl. unfold locl in *. simpl in *. intros. assert (Hlocl' := Hlocl k d). congruence.
      split.

      intros H. apply cmd_to_trm with efresh. apply H. apply Kle_eta_r. intros w2 w1w2 H2. apply sforces_correct_Disj in H2. case H2. intros case1. apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in case1. simpl. apply to_cmd with (Disj A1 A2). destruct case1 as [t1 Ht1]. exists (injl t1). constructor. exact Ht1.

      exists (e_var efresh). constructor. apply w1w2. simpl. left;reflexivity. intros case2. apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)) in case2. simpl. apply to_cmd with (Disj A1 A2). destruct case2 as [t2 Ht2]. exists (injr t2). constructor. exact Ht2.

      exists (e_var efresh).
      constructor.
      apply w1w2.
      simpl.
      left;reflexivity.

      intros H. set (w1 := ((tfresh, A1)::fst w, snd w)). assert (ww1 : wle w w1). apply Kle_eta_l.
      assert (branch1 : Normal_ect A1 (fst w1) (snd w1)).
        apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)). intros w' w1w' H'. apply H. eauto using wle_trans. apply sforces_correct_Disj'. left. apply ret. assumption. set (w2 := ((tfresh, A2)::fst w, snd w)).
      assert (ww2 : wle w w2).
        apply Kle_eta_l. assert (branch2 : Normal_ect A2 (fst w2) (snd w2)). apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)). intros w' w2w' H'. apply H. eauto using wle_trans. apply sforces_correct_Disj'. right. apply ret.
      assumption.
      destruct branch1 as [e1 He1].
      destruct branch2 as [e2 He2].
      exists (disj (mut tfresh (cm (t_var tfresh) e1)) 
                  (mut tfresh (cm (t_var tfresh) e2))).
      
      constructor. constructor.  apply Cut with A1.
      constructor. left;reflexivity. assumption. constructor. 
      apply Cut with A2. constructor. left;reflexivity. assumption.
    + (* Conjunction *)
    (* copy paste *)
      assert (Hdepth2 : le (depth A2) n).
        clear -HSn. simpl in HSn. apply le_S_n in HSn. eapply le_trans. apply le_max_r. apply HSn. 
      assert (Hdepth1 : le (depth A1) n).
        clear -HSn. simpl in HSn. apply le_S_n in HSn. eapply le_trans. apply le_max_l. apply HSn.
      assert (Hlocl1 : locl A1).
        clear -Hlocl. unfold locl in *. simpl in *. intros. assert (Hlocl' := Hlocl k d). congruence.
      assert (Hlocl2 : locl A2).
        clear -Hlocl. unfold locl in *. simpl in *. intros. assert (Hlocl' := Hlocl k d). congruence.
      split.

    intros H.
    assert (conj1 : Normal_trm A1 (fst w) (snd w)).
      apply cmd_to_trm with efresh. apply H. apply Kle_eta_r. intros w2 w1w2 H2. apply sforces_correct_Conj in H2. destruct H2 as [Ht1 _].
      apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in Ht1. destruct Ht1 as [t1 Ht1]. exists (cm t1 (e_var efresh)). apply Cut with A1. assumption. constructor. apply w1w2. left;reflexivity.
    assert (conj2 : Normal_trm A2 (fst w) (snd w)).
      apply cmd_to_trm with efresh. apply H. apply Kle_eta_r. intros w2 w1w2 H2. apply sforces_correct_Conj in H2. destruct H2 as [_ Ht2].
      apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)) in Ht2. destruct Ht2 as [t2 Ht2]. exists (cm t2 (e_var efresh)). apply Cut with A2. assumption. constructor. apply w1w2. left;reflexivity.
    destruct conj1 as [t1' Ht1'].
    destruct conj2 as [t2' Ht2'].
    exists (paire t1' t2').
    constructor. assumption. assumption.

    intros H. apply cmd_to_ect with (tfresh). apply H. apply Kle_eta_l. apply sforces_correct_Conj'. clear H. split.
    intros w2 w1w2 k. change (w2:A1||-) in k. 
    apply (IHn _ Hdepth1 Hlocl1 _ (S tfresh) (S efresh)) in k.
    destruct k as [e1 He1].
    exists (cm (t_var tfresh) (projl e1)). apply Cut with (Conj A1 A2). constructor. apply w1w2. left;reflexivity.

    constructor. assumption. intros w2 w1w2 k. change (w2:A2||-) in k. apply (IHn _ Hdepth2 Hlocl2 _ (S tfresh) (S efresh)) in k. destruct k as [e2 He2]. exists (cm (t_var tfresh) (projr e2)). apply Cut with (Conj A1 A2). constructor. apply w1w2. left;reflexivity.
    constructor.
    assumption.
    + (* First order logic stuff now, *)
      (* Universal quantifier *)
      split. intros H. set (L := FV_typ A ++ FV_cxt (fst w) ++ FV_cxt (snd w)). assert (H0:forall y:var_free, y \notin L -> Normal_trm (A^y) (fst w) (snd w)). intros. apply cmd_to_trm with efresh. 
      ++ apply H. apply Kle_eta_r. intros w2 w1w2 HAllA. assert (HAllA' := sforces_correct_All HAllA). clear HAllA.
    assert (Hdepth' : le (depth (A^y)) n).
      clear -HSn. simpl in HSn. rewrite depth_subst. apply le_S_n in HSn. assumption.
    assert (Hlocl' : locl (A^y)).
      apply locl_locli_subst'. assumption. apply locli_free_var.
    assert (HAd : w2  : ||- A^y).
    apply HAllA'. clear HAllA'. apply wle_refl. apply locli_free_var. apply (IHn _ Hdepth' Hlocl' _ (S tfresh) (S efresh)) in HAd. destruct HAd as [td Htd]. exists (cm td (e_var efresh)). apply Cut with (A^y). assumption. apply AxL. apply w1w2. left;reflexivity.
      ++ apply proof_trm_quant_invar in H0. destruct H0 as [s Hs]. exists (tall s). apply AllR with L. assumption. intros. apply Hs. assumption.
      ++ intros H. apply cmd_to_ect with tfresh. apply H. apply Kle_eta_l. apply sforces_correct_All'. intros w2 w1w2 d Hd. intros w3 w2w3 HAd. change (w3:A^^d||-) in HAd.
      assert (Hdepth' : le (depth (A^^d)) n).
        clear -HSn. simpl in HSn. rewrite depth_subst. apply le_S_n in HSn. assumption.
      assert (Hlocl' : locl (A^^d)).
        apply locl_locli_subst'. assumption. assumption.
      apply (IHn _ Hdepth' Hlocl' _ (S tfresh) (S efresh)) in HAd.
      destruct HAd as [ed Hed]. exists (cm (t_var tfresh) (eall ed)). apply Cut with (All A). constructor. apply w2w3. apply w1w2. left;reflexivity. apply AllL with d. assumption. assumption.
    + 
    (* Existential *)
    (* I claim this is similar and because I am short on time I will not prove it since we are already admitting ; but it should be the same as forall but with a few axioms flipped. For a paper proof see Aris' notes. *)
Admitted.