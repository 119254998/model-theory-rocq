From Stdlib Require Import List Arith.
Import ListNotations.
Set Implicit Arguments.

(*
The aim is to overload Coq standard library functions
for prop to Type functions

We are literally copy pasting the Yale prover's 
implementation of these functions and changing 
the type by the way
*)

Section Le_Overloaded.
    Inductive le (n:nat): nat -> Set :=
    | le_n: le n n
    | le_S: forall m:nat, le n m -> le n (S m).

    Notation "n <= m" := (le n m) : type_scope.

    Lemma le_trans : forall n m p, le n m -> le m p -> le n p.
    Proof.
    intros. induction H0.
    - apply H.
    - constructor. apply IHle.
    Qed.
    Hint Resolve le_trans : arith v62.

    Theorem le_n_S : forall n m, n <= m -> S n <= S m.
    Proof.
        induction 1; auto.
        constructor.
        constructor.
        assumption.
    Defined.

    Theorem le_S_n : forall n m, S n <= S m -> n <= m.
    Proof.
        intros n m H; change (pred (S n) <= pred (S m)) in |- *.
        destruct H; simpl; auto with arith.
        constructor.
        apply le_trans with (S n).
        constructor.
        constructor.
        assumption.
    Defined.
    
    Theorem le_O_n : forall n, 0 <= n.
    Proof.
        induction n.
        constructor.
        constructor.
        assumption.
    Defined.
    
    Lemma max_l : forall n m, m <= n -> max n m = n.
    Proof.
        induction n; induction m; simpl in |- *; auto with arith.
        intro H.
        inversion H.
        intro H.
        assert (max n m = n).
        apply IHn.
        inversion H.
        constructor.
        eapply le_trans.
        apply le_S.
        apply le_n.
        assumption.
        rewrite H0.
        reflexivity.
    Defined.

    Lemma max_r : forall n m, n <= m -> max n m = m.
    Proof.
        induction n; induction m; simpl in |- *; auto with arith.
        intro H.
        inversion H.
        intro H.
        assert (max n m = m).
        apply IHn.
        inversion H.
        constructor.
        eapply le_trans.
        apply le_S.
        apply le_n.
        assumption.
        rewrite H0.
        reflexivity.
    Defined.

    Lemma le_max_l : forall n m, n <= max n m.
    Proof.
        induction n; induction m; intros; auto with arith.
        constructor.
        constructor.
        assumption.
        constructor.
        simpl.
        apply le_n_S.
        auto.
    Defined.
    
    Lemma le_max_r : forall n m, m <= max n m.
    Proof.
        induction n; simpl in |- *; auto with arith.
        intro.
        constructor.
        induction m; simpl in |- *; auto with arith.
        apply le_O_n.
        apply le_n_S.
        auto.
    Defined.

    Lemma le_self : forall n, n <= n.
    Proof.
        intros. constructor.
    Qed.

End Le_Overloaded.

Section In_Overloaded.
    Variable X: Type.
    Open Scope type_scope.

    Fixpoint In (a: X) (l: list X) {struct l} : Set :=
        match l with
        | nil => Empty_set
        | b :: m => (b=a) + In a m
        end.

    
  Definition incl (l m:list X) := forall a:X, In a l -> In a m.
  Hint Unfold incl.
  
  Lemma incl_refl : forall l:list X, incl l l.
  Proof.
    auto.
  Defined.
  Hint Resolve incl_refl.
  
  Lemma incl_tran : forall l m n:list X, incl l m -> incl m n -> incl l n.
  Proof.
    auto.
  Defined.

  Hint Unfold incl.
  Hint Resolve incl_refl.
  Lemma cons_incl_head : forall l1 l2:list X, forall a:X,
    incl l1 l2 -> incl (a::l1) (a::l2).
  Proof.
    intros l1 l2 a H.
    red;simpl.
    intros b H1.
    destruct H1.
    left; assumption.
    right.
    apply H.
    assumption.
  Defined.

  Lemma in_or_app : forall (l m:list X) (a:X), In a l + In a m -> In a (l ++ m).
  Proof. 
    intros l m a.
    elim l; simpl in |- *; intro H.
    now_show (In a m).
    elim H; auto; intro H0.
    now_show (In a m).
    elim H0. (* subProof completed *)
    intros y H0 H1.
    now_show ((H = a) + In a (y ++ m)).
    elim H1; auto 4.
    intro H2.
    now_show ((H = a) + In a (y ++ m)).
    elim H2; auto.
  Defined.

  Variable f : X -> bool.

  Lemma forallb_forall : 
    forall l, forallb f l = true <-> (forall x, In x l -> f x = true).
  Proof.
    induction l; simpl; intuition.
    destruct (andb_prop _ _ H1).
    congruence.
    destruct (andb_prop _ _ H1); auto.
    assert (forallb f l = true).
    apply H0; intuition.
    rewrite H1; auto. 
  Defined.
End In_Overloaded.

Hint Unfold incl.
Hint Unfold In.
Hint Resolve incl_refl.

Section iff_Type.
  Open Scope type_scope.
  Definition iff (A B:Type) := (A -> B) * (B -> A).
End iff_Type.
Notation "A <-> B" := (iff A B) : type_scope.
Hint Unfold iff: extcore.