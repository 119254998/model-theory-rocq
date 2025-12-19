(* 
Going to allow importing Peano_dec here 
because it only contains decidability results 
for natural numbers,
which are often useful in basic developments.
*)
From Stdlib Require Import Peano_dec EqNat.
From FOL Require Import overloadedbullshit.
From Stdlib Require Import List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope type_scope.

Definition var_term := nat. (* We will use De Bruijn indices for variable terms; relevant because weak PA utilizes N as its domain and this could eventually work towards a Godel 1 proof *)
Definition var_ect := nat. (* Similarly, nat. Remember we are using kripke now! *)

(*
Basically, this means that we have 2 layers of variables
1. Bound variables, which are represented by De Bruijn indices (nat)
2. Free variables, which are represented by nat as well (but these nats represent variable names, not indices)

Then, we are supposed to declare some kind of freshness axiom, 

fresh_fvar : forall L, sigT (fun x => x \notin L).

which states that for any finite set of variable names L,
there exists a variable name x that is not in L. (so there's always a new variable to be had)

Also, in kripke arity is not enforced by any type system and well formedness is a syntactic notion. In our Tarski one we had dependent types enforcing arity.

The goal is to build a kripke bridge to tarski's fol.
*)

Inductive command : Set :=
| cm : term -> ect -> command
with term : Set :=
| t_var  : var_term -> term
| lambda   : var_term -> term -> term
| injl  : term -> term
| injr  : term -> term
| paire : term -> term -> term
| mu    : var_ect -> command -> term
| tall  : term -> term
| texist   : term -> term
with ect : Set :=
| e_var  : var_ect -> ect
| app   : term -> ect -> ect
| disj  : ect -> ect -> ect
| projl : ect -> ect
| projr : ect -> ect
| mut   : var_term -> command -> ect
| eall  : ect -> ect
| eexist   : ect -> ect.


Parameter var_free : Set.
Parameter var_free_dec : forall x y : var_free, {x = y} + {x <> y}. (* decidability of free variable equality *)

Parameters predicate function: Set (* sets of predicate and function symbols *).

Notation "x \notin L" := (In x L -> Empty_set) (at level 70).
Notation "x \in L" := (In x L) (at level 70).

Axiom fresh_free_var : forall L, sigT (fun x : var_free => x \notin L).

(*
De Bruijn
*)
Inductive indiv : Set :=
| bound_var : nat -> indiv
| free_var : var_free -> indiv
| func : function -> list indiv -> indiv.

Inductive typ : Set :=
| Atom : predicate -> list indiv -> typ
| Imp  : typ -> typ -> typ
| Disj : typ -> typ -> typ
| Conj : typ -> typ -> typ
| All  : typ -> typ
| Ex   : typ -> typ.

(** Substituting at de Bruijn variable k *) 

Fixpoint subst_indiv (n : nat) (a : indiv) (d : indiv) {struct a} : indiv :=
  let subst_list := fix subst_list (l:list indiv) {struct l} : list indiv :=
    match l with
      | nil => nil
      | a' :: l' => subst_indiv n a' d :: subst_list l'
    end in
  match a with
    | func f ld => 
      func f (subst_list ld)
    | free_var x => free_var x
    | bound_var i => if Nat.eqb n i then d else bound_var i
  end.

Fixpoint subst (n : nat) (A : typ)(d : indiv) {struct A} : typ :=
  let subst_list := fix subst_list (l : list indiv) {struct l} : list indiv :=
    match l with
      | nil => nil
      | a' :: l' => subst_indiv n a' d :: subst_list l'
    end in
  match A with
    | Atom p l   => Atom p (subst_list l)
    | Imp A1 A2  => Imp (subst n A1 d) (subst n A2 d)
    | Conj A1 A2 => Conj (subst n A1 d) (subst n A2 d)
    | Disj A1 A2 => Disj (subst n A1 d) (subst n A2 d)
    | All A1     => All (subst (S n) A1 d)
    | Ex A1      => Ex (subst (S n) A1 d)
  end.

Notation "A ^^ d" := (subst 0 A d) (at level 67).
Notation "A ^ x" := (subst 0 A (free_var x)).

(** 
If a term or ect is invariant under substitution it's called a locally invariant term. See Aris' notes for details on free vs bound variables. 
*)
Definition locl (A:typ) := forall k d, (subst k A d) = A.
Definition locli (d':indiv) := forall k d, (subst_indiv k d' d) = d'.

Definition cxt_trm := list (var_term * typ).
Definition cxt_ect := list (var_ect * typ).

Reserved Notation "c : ( Gamma |- Delta ) " (at level 70).
Reserved Notation "Gamma |- ( t : A ) ; Delta" 
  (at level 70, A at next level, t at next level).
Reserved Notation "Gamma ; ( e : A ) |- Delta" 
  (at level 70, A at next level, e at next level).

(** random code ideas I stole from online see citation *)
Inductive proof_cmd : command -> cxt_trm -> cxt_ect -> Set :=
| Cut v e Gamma Delta A :
  proof_trm Gamma v A Delta ->
  proof_ect Gamma e A Delta ->
  proof_cmd (cm v e) Gamma Delta

where "c : ( Gamma |- Delta )" := (proof_cmd c Gamma Delta)

with proof_trm : cxt_trm -> term -> typ -> cxt_ect -> Set :=
| AxR Gamma a A Delta : 
  In (a,A) Gamma -> 
  proof_trm Gamma (t_var a) A Delta

| Mu Gamma alpha c A Delta :
  proof_cmd c Gamma ((alpha,A)::Delta) ->
  proof_trm Gamma (mu alpha c) A Delta

| ImpR Gamma a t A B Delta :
  proof_trm ((a,A)::Gamma) t B Delta ->
  proof_trm Gamma (lambda a t) (Imp A B) Delta

| DisjRL Gamma v A1 A2 Delta :
  proof_trm Gamma v A1 Delta ->
  proof_trm Gamma (injl v) (Disj A1 A2) Delta

| DisjRR Gamma v A1 A2 Delta :
  proof_trm Gamma v A2 Delta ->
  proof_trm Gamma (injr v) (Disj A1 A2) Delta

| ConjR Gamma v1 v2 A1 A2 Delta :
  proof_trm Gamma v1 A1 Delta ->
  proof_trm Gamma v2 A2 Delta ->
  proof_trm Gamma (paire v1 v2) (Conj A1 A2) Delta

| AllR Gamma t A Delta L :
  locl (All A) ->
  (forall x, x \notin L -> proof_trm Gamma t (A^x) Delta) ->
  proof_trm Gamma (tall t) (All A) Delta

| ExR Gamma t A Delta d : locli d ->
  proof_trm Gamma t (A^^d) Delta ->
  proof_trm Gamma (texist t) (Ex A) Delta

where "Gamma |- ( t : A ) ; Delta" := (proof_trm Gamma t A Delta)
  
with proof_ect : cxt_trm -> ect -> typ -> cxt_ect -> Set :=
| AxL Gamma alpha A Delta :
  In (alpha,A) Delta ->
  proof_ect Gamma (e_var alpha) A Delta

| MuT Gamma a c A Delta :
  proof_cmd c ((a,A)::Gamma) Delta ->
  proof_ect Gamma (mut a c) A Delta

| ImpL Gamma v e A B Delta :
  proof_trm Gamma v A Delta ->
  proof_ect Gamma e B Delta ->
  proof_ect Gamma (app v e) (Imp A B) Delta

| DisjL Gamma e1 e2 A1 A2 Delta :
  proof_ect Gamma e1 A1 Delta -> 
  proof_ect Gamma e2 A2 Delta ->
  proof_ect Gamma (disj e1 e2) (Disj A1 A2) Delta

| ConjLL Gamma e A1 A2 Delta :
  proof_ect Gamma e A1 Delta ->
  proof_ect Gamma (projl e) (Conj A1 A2) Delta

| ConjLR Gamma e A1 A2 Delta :
  proof_ect Gamma e A2 Delta ->
  proof_ect Gamma (projr e) (Conj A1 A2) Delta

| AllL Gamma e A Delta d : locli d ->
  proof_ect Gamma e (A^^d) Delta ->
  proof_ect Gamma (eall e) (All A) Delta

| ExL Gamma e A Delta L :
  locl (Ex A) ->
  (forall x, x \notin L -> proof_ect Gamma e (A^x) Delta) ->
  proof_ect Gamma (eexist e) (Ex A) Delta

where "Gamma ; ( e : A ) |- Delta" := (proof_ect Gamma e A Delta)
.

(*
It turns out we need to overload the induction scheme anyway
because we need to use it in a way that is not compatible with the standard induction scheme.
*)

Scheme proof_cmd_rect' := Induction for proof_cmd Sort Type
with proof_trm_rect' := Induction for proof_trm Sort Type
with proof_ect_rect' := Induction for proof_ect Sort Type.

(*
Stolen from A Logically Saturated Extension of ${{\bar\lambda\mu\tilde{\mu}}}$ cw https://link.springer.com/chapter/10.1007/978-3-642-02614-0_32
*)
Definition proof_rect' := fun
  (P : forall (c : command) (c0 : cxt_trm) (c1 : cxt_ect),
       proof_cmd c c0 c1 -> Type)
  (P0 : forall (c : cxt_trm) (t : term) (t0 : typ) (c0 : cxt_ect),
        proof_trm c t t0 c0 -> Type)
  (P1 : forall (c : cxt_trm) (e : ect) (t : typ) (c0 : cxt_ect),
        proof_ect c e t c0 -> Type)
  (f : forall (v : term) (e : ect) (Gamma : cxt_trm) 
         (Delta : cxt_ect) (A : typ) (p : proof_trm Gamma v A Delta),
       P0 Gamma v A Delta p ->
       forall p0 : proof_ect Gamma e A Delta,
       P1 Gamma e A Delta p0 -> P (cm v e) Gamma Delta (Cut p p0))
  (f0 : forall (Gamma : list (prod var_term typ)) (a : var_term) 
          (A : typ) (Delta : cxt_ect) (i : In (pair a A) Gamma),
        P0 Gamma (t_var a) A Delta (AxR (Gamma:=Gamma) (a:=a) (A:=A) Delta i))
  (f1 : forall (Gamma : cxt_trm) (alpha : var_ect) 
          (c : command) (A : typ) (Delta : list (prod var_ect typ))
          (p : proof_cmd c Gamma (cons (pair alpha A) Delta)),
        P c Gamma (cons (pair alpha A) Delta) p ->
        P0 Gamma (mu alpha c) A Delta (Mu p))
  (f2 : forall (Gamma : list (prod var_term typ)) (a : var_term) 
          (t : term) (A B : typ) (Delta : cxt_ect)
          (p : proof_trm (cons (pair a A) Gamma) t B Delta),
        P0 (cons (pair a A) Gamma) t B Delta p ->
        P0 Gamma (lambda a t) (Imp A B) Delta (ImpR p))
  (f3 : forall (Gamma : cxt_trm) (v : term) (A1 A2 : typ) 
          (Delta : cxt_ect) (p : proof_trm Gamma v A1 Delta),
        P0 Gamma v A1 Delta p ->
        P0 Gamma (injl v) (Disj A1 A2) Delta (DisjRL A2 p))
  (f4 : forall (Gamma : cxt_trm) (v : term) (A1 A2 : typ) 
          (Delta : cxt_ect) (p : proof_trm Gamma v A2 Delta),
        P0 Gamma v A2 Delta p ->
        P0 Gamma (injr v) (Disj A1 A2) Delta (DisjRR A1 p))
  (f5 : forall (Gamma : cxt_trm) (v1 v2 : term) (A1 A2 : typ)
          (Delta : cxt_ect) (p : proof_trm Gamma v1 A1 Delta),
        P0 Gamma v1 A1 Delta p ->
        forall p0 : proof_trm Gamma v2 A2 Delta,
        P0 Gamma v2 A2 Delta p0 ->
        P0 Gamma (paire v1 v2) (Conj A1 A2) Delta (ConjR p p0))
  (f6 : forall (Gamma : cxt_trm) (t : term) (A : typ) 
          (Delta : cxt_ect) (L : list var_free) (l : locl (All A))
          (p : forall x : var_free,
               (In x L -> Empty_set) ->
               proof_trm Gamma t (subst O A (free_var x)) Delta),
        (forall (x : var_free) (e : In x L -> Empty_set),
         P0 Gamma t (subst O A (free_var x)) Delta (p x e)) ->
        P0 Gamma (tall t) (All A) Delta (AllR (A:=A) (L:=L) l p))
  (f7 : forall (Gamma : cxt_trm) (t : term) (A : typ) 
          (Delta : cxt_ect) (d : indiv) (l : locli d)
          (p : proof_trm Gamma t (subst O A d) Delta),
        P0 Gamma t (subst O A d) Delta p ->
        P0 Gamma (texist t) (Ex A) Delta (ExR (A:=A) (d:=d) l p))
  (f8 : forall (Gamma : cxt_trm) (alpha : var_ect) 
          (A : typ) (Delta : list (prod var_ect typ))
          (i : In (pair alpha A) Delta),
        P1 Gamma (e_var alpha) A Delta
          (AxL Gamma (alpha:=alpha) (A:=A) (Delta:=Delta) i))
  (f9 : forall (Gamma : list (prod var_term typ)) (a : var_term) 
          (c : command) (A : typ) (Delta : cxt_ect)
          (p : proof_cmd c (cons (pair a A) Gamma) Delta),
        P c (cons (pair a A) Gamma) Delta p ->
        P1 Gamma (mut a c) A Delta (MuT p))
  (f10 : forall (Gamma : cxt_trm) (v : term) (e : ect) 
           (A B : typ) (Delta : cxt_ect) (p : proof_trm Gamma v A Delta),
         P0 Gamma v A Delta p ->
         forall p0 : proof_ect Gamma e B Delta,
         P1 Gamma e B Delta p0 ->
         P1 Gamma (app v e) (Imp A B) Delta (ImpL p p0))
  (f11 : forall (Gamma : cxt_trm) (e1 e2 : ect) (A1 A2 : typ)
           (Delta : cxt_ect) (p : proof_ect Gamma e1 A1 Delta),
         P1 Gamma e1 A1 Delta p ->
         forall p0 : proof_ect Gamma e2 A2 Delta,
         P1 Gamma e2 A2 Delta p0 ->
         P1 Gamma (disj e1 e2) (Disj A1 A2) Delta (DisjL p p0))
  (f12 : forall (Gamma : cxt_trm) (e : ect) (A1 A2 : typ) 
           (Delta : cxt_ect) (p : proof_ect Gamma e A1 Delta),
         P1 Gamma e A1 Delta p ->
         P1 Gamma (projl e) (Conj A1 A2) Delta (ConjLL A2 p))
  (f13 : forall (Gamma : cxt_trm) (e : ect) (A1 A2 : typ) 
           (Delta : cxt_ect) (p : proof_ect Gamma e A2 Delta),
         P1 Gamma e A2 Delta p ->
         P1 Gamma (projr e) (Conj A1 A2) Delta (ConjLR A1 p))
  (f14 : forall (Gamma : cxt_trm) (e : ect) (A : typ) 
           (Delta : cxt_ect) (d : indiv) (l : locli d)
           (p : proof_ect Gamma e (subst O A d) Delta),
         P1 Gamma e (subst O A d) Delta p ->
         P1 Gamma (eall e) (All A) Delta (AllL (A:=A) (d:=d) l p))
  (f15 : forall (Gamma : cxt_trm) (e : ect) (A : typ) 
           (Delta : cxt_ect) (L : list var_free) (l : locl (Ex A))
           (p : forall x : var_free,
                (In x L -> Empty_set) ->
                proof_ect Gamma e (subst O A (free_var x)) Delta),
         (forall (x : var_free) (e0 : In x L -> Empty_set),
          P1 Gamma e (subst O A (free_var x)) Delta (p x e0)) ->
         P1 Gamma (eexist e) (Ex A) Delta (ExL (A:=A) (L:=L) l p)) =>
  pair 
  (pair 
    (proof_cmd_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
      f10 f11 f12 f13 f14 f15)
    (proof_trm_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8
      f9 f10 f11 f12 f13 f14 f15))
  (proof_ect_rect' (P:=P) (P0:=P0) (P1:=P1) f f0 f1 f2 f3 f4 f5 f6 f7 f8
    f9 f10 f11 f12 f13 f14 f15).

Section Abstract_Semantics.
  (** 
  The kripke style semantics of the logic. 

  We want a forcing relation [aforces] that takes a world w, a predicate P, and a list of individual terms ld, and returns a proposition that is true when the predicate P holds of the individuals in ld in the world w.

  wle is a partial order on the set of worlds, and [exploding] is a predicate that tells us when a world is exploding. A world w is exploding when it forces every formula.
  *)
  Record Kripke : Type := {
    world :> Set;
    wle : world -> world -> Type;
    wle_refl : forall w, wle w w;
    wle_trans : forall w y z, wle w y -> wle y z -> wle w z;
    exploding : world -> Set;
    aforces : world -> predicate -> list indiv -> Set;
    aforces_mon : forall w P ld, @aforces w P ld -> 
      forall z, wle w z -> @aforces z P ld
  }.
  (*
  WOw, the third time we're overloading this!
  *)
  Notation "w <= z" := (wle w z).

  Variable K:Kripke.

  (** The continuations monad *)
  Definition Kont (F : K -> typ -> Type) (w : K) (A : typ) := 
    forall w1, w <= w1 -> 
      (forall w2, w1 <= w2 -> F w2 A -> exploding w2) -> exploding w1.
  Hint Unfold Kont. (* using systems is overrated *)

  (** Strong forcing extended to composite formulas. We use Kont sforces for
  weak forcing *)
  Fixpoint sforces' (n:nat)(w:K)(A:typ) {struct n} : Type :=
    match n with
      | O => Empty_set
      | S m => 
        match A with
          | Atom P ld  => aforces w P ld
          | Imp A1 A2  => forall w', w <= w'-> Kont (sforces' m) w' A1 -> Kont (sforces' m) w' A2
          | Disj A1 A2 => Kont (sforces' m) w A1 + Kont (sforces' m) w A2
          | Conj A1 A2 => Kont (sforces' m) w A1 * Kont (sforces' m) w A2
          | All A1     => forall w', w <= w' -> forall d, locli d -> Kont (sforces' m) w' (A1^^d)
          | Ex A1      => sigT (fun d => (locli d) * Kont (sforces' m) w (A1^^d))
        end
    end.

  Fixpoint depth (A:typ) : nat :=
    match A with
      | Atom _ _   => 1
      | Imp A1 A2  => S (max (depth A1) (depth A2))
      | Disj A1 A2 => S (max (depth A1) (depth A2))
      | Conj A1 A2 => S (max (depth A1) (depth A2))
      | All A1     => S (depth A1)
      | Ex A1      => S (depth A1)
    end.

  Definition sforces (w : K) (A : typ) := sforces' (depth A) w A.
  Hint Unfold sforces.

  (** 
  We do not need to prove that sforces is monotonic, because it's a consequence of the definition of sforces'.  However, we need to prove that sforces' is monotonic in its first argument. We will use this to show that sforces is monotonic in its first argument.
  *)
  Section sforces_correctness.
    Theorem depth_subst : forall A d k, depth (subst k A d) = depth A.
    Proof.
      induction A; simpl; intros.
      
      reflexivity.
      
      rewrite IHA1 with d k.
      rewrite IHA2 with d k.
      reflexivity.
      
      rewrite IHA1 with d k.
      rewrite IHA2 with d k.
      reflexivity.
      
      rewrite IHA1 with d k.
      rewrite IHA2 with d k.
      reflexivity.
      
      rewrite IHA with d (S k).
      reflexivity.

      rewrite IHA with d (S k).
      reflexivity.
    Qed.

    (*
    This is actually not useful
    *)

    Definition iffT (P Q : Type) : Type := (P -> Q) * (Q -> P).
    (*
    
    I have not the foggiest clue how to prove this. I think it's clearly true
    (we are just saying that if we have a proof of sforces' n w A then we also have a proof of sforces' (S n) w A), but I got stuck on the induction. 
    *)
    Theorem sforces'_S :
    forall n A w,
      le (depth A) n -> 
      (sforces' n w A <-> sforces' (S n) w A).
    Proof.
      admit.
    Admitted.

    (*
    sforces s1 is the first half of sforces. It's used to prove that sforces is monotonic in its first argument. Similarly sforces'_S2 is the second half.
    *)
    Definition sforces'_S1 := fun n A w Hle => fst (@sforces'_S n A w Hle).
    Definition sforces'_S2 := fun n A w Hle => snd (@sforces'_S n A w Hle).

    Theorem sforces'_mon1 : forall n m, le n m -> 
      forall A, le (depth A) n -> forall w, sforces' n w A -> sforces' m w A.
    Proof.
      intros n m Hle. induction Hle.
      - auto.
      - intros. apply sforces'_S1. eauto using le_trans. auto.
    Qed.

    Theorem sforces'_mon2 : forall n m, le n m -> 
      forall A, le (depth A) n -> forall w, sforces' m w A -> sforces' n w A.
    Proof.
      intros n m H. induction H.
      - auto.
      - intros. apply IHle.
        + auto.
        +  apply sforces'_S2.
          eauto using le_trans.
          assumption.
    Qed.

    Theorem Kont_invariant : forall F1 F2 : K -> typ -> Type, forall A,
      (forall w, F1 w A -> F2 w A) -> forall w, Kont F1 w A -> Kont F2 w A.
    Proof.
      intros F1 F2 A HF1F2 w HF1 w1 ww1 k1.
      apply HF1.
      - auto.
      - intros w2 w1w2 HF1'. apply k1. auto. auto.
    Qed.

    Theorem sforces_correct_Atom : forall w P ld,
      sforces w (@Atom P ld) -> aforces w P ld.
    Proof.
      unfold sforces. auto.
    Qed.

    Theorem sforces_correct_Atom' : forall w P ld,
      aforces w P ld -> sforces w (@Atom P ld).
    Proof.
      unfold sforces. auto.
    Qed.

    Theorem sforces_correct_Disj : forall w A B, sforces w (Disj A B) -> 
      Kont sforces w A + Kont sforces w B.
    Proof.
      intros w A B H. unfold sforces in H. simpl in H. destruct H.
      - left. change (Kont (sforces' (depth A)) w A). generalize dependent k. apply Kont_invariant. intros w'. apply sforces'_mon2. apply le_max_l. constructor.
      - right. change (Kont (sforces' (depth B)) w B). generalize dependent k. apply Kont_invariant. intros w'. apply sforces'_mon2. apply le_max_r. constructor.
    Qed.

    Theorem sforces_correct_Disj' : forall w A B, 
      Kont sforces w A + Kont sforces w B -> sforces w (Disj A B).
    Proof.
      intros w A B H. destruct H. unfold sforces. simpl.
      - left. generalize dependent k. apply Kont_invariant. intros w'. apply sforces'_mon1. apply le_max_l. constructor.
      - right. generalize dependent k. apply Kont_invariant. intros w'. apply sforces'_mon1. apply le_max_r. constructor.
    Qed.

    Theorem sforces_correct_Conj : forall w A B, sforces w (Conj A B) -> 
      Kont sforces w A * Kont sforces w B.
    Proof.
      intros w A B H. unfold sforces in H. simpl in H. destruct H. split.
      - change (Kont (sforces' (depth A)) w A). generalize dependent k. apply Kont_invariant. intros w'. apply sforces'_mon2. apply le_max_l. constructor.
      - change (Kont (sforces' (depth B)) w B). generalize dependent k0. apply Kont_invariant. intros w'. apply sforces'_mon2. apply le_max_r. constructor. 
    Qed.

    Theorem sforces_correct_Conj' : forall w A B,  
      Kont sforces w A * Kont sforces w B -> sforces w (Conj A B).
    Proof.
      intros w A B H. unfold sforces. simpl. destruct H. split.
      - generalize dependent k. apply Kont_invariant. intros w'. apply sforces'_mon1. apply le_max_l. constructor.
      - generalize dependent k0. apply Kont_invariant. intros w'. apply sforces'_mon1. apply le_max_r. constructor.
    Qed.

    Theorem sforces_correct_Imp : forall w A B, sforces w (Imp A B) -> 
      forall w', w <= w' -> Kont sforces w' A -> Kont sforces w' B.
    Proof.
      intros w A B H. unfold sforces in H. simpl in H. intros w' ww' HA.

      change (Kont (sforces' (depth A)) w' A) in HA.
      change (Kont (sforces' (depth B)) w' B).

      apply Kont_invariant with (sforces' (max (depth A) (depth B))).
      apply sforces'_mon2.
      apply le_max_r.
      constructor.
      apply H.
      assumption.
      generalize dependent HA.
      apply Kont_invariant.
      apply sforces'_mon1.
      apply le_max_l.
      constructor.
    Qed.

    Theorem sforces_correct_Imp' : forall w A B,  
      (forall w', w <= w' -> Kont sforces w' A -> Kont sforces w' B)
        -> sforces w (Imp A B).
    Proof.
      intros w A B H. unfold sforces. simpl. intros w' ww' HA.

      apply Kont_invariant with (sforces' (depth B)). intros w''. apply sforces'_mon1. apply le_max_r. constructor. apply H. assumption. generalize dependent HA. apply Kont_invariant. apply sforces'_mon2. apply le_max_l. constructor.
    Qed.

    Theorem sforces_correct_All : forall w A, sforces w (All A) -> 
      forall w', w <= w' -> forall d, locli d -> Kont sforces w' (A^^d).
    Proof.
      intros w A H. unfold sforces in H. simpl in H. intros w' ww' d Hd.

      change (Kont (sforces' (depth (A^^d))) w' (A^^d)).
      assert (H' := H w' ww' d Hd).
      generalize dependent H'.
      apply Kont_invariant.
      apply sforces'_mon2.
      rewrite depth_subst.
      constructor.
      constructor.
    Qed.

    Theorem sforces_correct_All' : forall w A, 
      (forall w', w <= w' -> forall d, locli d -> Kont sforces w' (A^^d))
      -> sforces w (All A).
    Proof.
      intros w A H. unfold sforces. simpl. intros w' ww' d Hd.
      rewrite <- depth_subst with A d 0. apply H. auto. auto.
    Qed.

    Theorem sforces_correct_Ex : forall w A, sforces w (Ex A) -> 
      sigT (fun d => (locli d) * Kont sforces w (A^^d)).
    Proof.
      intros w A H. unfold sforces in H. simpl in H. destruct H as [d [Hd H]].

      exists d.
      split; [assumption|].
      change (Kont (sforces' (depth (A^^d))) w (A^^d)).
      generalize dependent H.
      apply Kont_invariant.
      apply sforces'_mon2.
      rewrite depth_subst.
      constructor.
      constructor.
    Qed.

    Theorem sforces_correct_Ex' : forall w A, 
      (sigT (fun d => (locli d) * Kont sforces w (A^^d)))
      -> sforces w (Ex A).
    Proof.
      intros w A H. unfold sforces. simpl. destruct H as [d [Hd H]].
      exists d.
      split; [assumption|].
      rewrite <- depth_subst with A d 0.
      apply H.
    Qed.
  End sforces_correctness.

  Definition refutes (w1:K)(A:typ) :=
      forall w2:K, w1 <= w2 -> sforces w2 A -> exploding w2.

  Notation "w : ||+ A " := (sforces w A) (at level 70).
  Notation "w : A ||- " := (refutes w A)  (at level 70).
  Notation "w : ||- A " := (Kont sforces w A) (at level 70).

  Fixpoint refutes_cxt (w:K)(Delta:cxt_ect) : Type :=
    match Delta with
      | nil => unit
      | cons aA Delta' => (refutes w (snd aA)) * (refutes_cxt w Delta')
    end.

  Fixpoint forces_cxt (w:K)(Gamma:cxt_trm) : Type :=
    match Gamma with
      | nil => unit
      | cons aA Gamma' => (w : ||- (snd aA)) * (forces_cxt w Gamma')
    end.

  Notation " w : ||-- Gamma" := (forces_cxt w Gamma) (at level 70).
  Notation " w : Delta ||-- "  := (refutes_cxt w Delta) (at level 70).

  Theorem sforces_mon : forall A w, w : ||+ A  -> forall w', w <= w' -> w' : ||+ A .
  Proof.
    induction A.

    unfold sforces.
    simpl.
    intros.
    eauto using aforces_mon.
    
    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    eauto using wle_trans.
    
    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    case H1; intro H'.
    left.
    eauto using wle_trans.
    eauto using wle_trans.
    
    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    destruct H1; split; eauto using wle_trans.

    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    eauto using wle_trans.

    unfold sforces.
    intros w H1 w' ww'.
    simpl in *.
    destruct H1 as [d [Hd H]].
    exists d.
    split; [assumption|].
    intros w1 w'w1 k.
    apply H.
    eauto using wle_trans.
    intros w2 w1w2 H2.
    auto.
  Qed.

  Definition ret {w A} : w : ||+ A -> w : ||- A.
  Proof.
  Admitted.


  Theorem refutes_mon : forall A w, w : A ||- -> forall w', w <= w' -> w' : A ||- .
  Proof.
    induction A; intros; unfold refutes in *; eauto using wle_trans.
  Qed.

  Theorem forces_mon : forall A w, w : ||- A -> forall w', w <= w' -> w' : ||- A.
  Proof.
    induction A; intros; eauto using wle_trans.
  Qed.

  Theorem refutes_cxt_mon : 
    forall Delta w, w : Delta ||-- -> forall w', w <= w' -> w' : Delta ||-- .
  Proof.
    induction Delta.
    simpl.
    auto.
    simpl.
    intros.
    destruct X.
    split; eauto using wle_trans,refutes_mon.
  Qed.

  Theorem forces_cxt_mon : 
    forall Gamma w, w : ||-- Gamma -> forall w', w <= w' -> w' : ||-- Gamma.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros.
    destruct X.
    split; eauto using wle_trans, forces_mon.
  Qed.

  (*
  I admit defeat
  *)
  Theorem refutes_cxt_In : forall w alpha A Delta, 
    In (alpha, A) Delta -> w : Delta ||-- -> w : A ||- .
  Proof.
  Admitted.

  Theorem forces_cxt_In : forall w x A Gamma, 
    In (x, A) Gamma -> w : ||-- Gamma -> w : ||- A.
  Proof.
    induction Gamma. simpl. intros. contradict H. simpl. intros H H0.
    admit. 
  Admitted.

  Theorem soundness : 
    (forall c Gamma Delta, c:(Gamma|-Delta) -> 
      forall w, w : ||-- Gamma -> w : Delta ||-- -> exploding w) *
    
    (forall Gamma t A Delta, Gamma|-(t:A);Delta -> 
      forall w, w : ||-- Gamma -> w : Delta ||-- -> w : ||- A) *
    
    (forall Gamma e A Delta, Gamma;(e:A)|-Delta -> 
      forall w, w : ||-- Gamma -> w : Delta ||-- -> w : A ||- ).
  Proof.
    apply proof_rect'.

    (* 
    Case Cut
    *)
    intros v e Gamma Delta A _ IH1 _ IH2.
    intros w HGamma HDelta.
    apply IH1 with w; auto.
    apply wle_refl.
    apply IH2; assumption.

    (* Ax *)
    intros.
    eauto using forces_cxt_In.

    (* Mu *)
    intros Gamma alpha c A Delta _ IH1 w H H0.
    intros w' ww' H1.
    apply IH1.
    eauto using forces_cxt_mon,wle_trans.
    simpl.
    eauto using refutes_cxt_mon,refutes_mon.

    (* Imp *)
    intros.
    apply ret.
    apply sforces_correct_Imp'.
    simpl in *.
    eauto using refutes_cxt_mon,forces_cxt_mon.
  
    (* Disj *)
    intros.
    apply ret.
    apply sforces_correct_Disj'.
    eauto using refutes_cxt_mon,forces_cxt_mon.

    (* Disj RR *)
    intros.
    apply ret.
    apply sforces_correct_Disj'.
    eauto using refutes_cxt_mon,forces_cxt_mon.

    (* Conj *)
    intros.
    apply ret.
    apply sforces_correct_Conj'.
    split;
      eauto using refutes_cxt_mon,forces_cxt_mon.

    (* Forall (this is complicated see Aris notes; it's hard to quantify over 
    something like this here) *)
    intros.
    apply ret.
    apply sforces_correct_All'.
    admit.

    (* Exists *)
    intros.
    apply ret.
    apply sforces_correct_Ex'.
    exists d.
    split; [assumption|].
    auto.

    (* Ax_L *)
    intros.
    eauto using refutes_cxt_In.

    (* MuT *)
    intros Gamma a c A Delta _ IH1.
    intros w H H0.
    intros w' ww' HA.
    apply IH1.
    simpl; split.
    apply ret; assumption.
    eauto using refutes_cxt_mon,forces_cxt_mon.
    eauto using refutes_cxt_mon,forces_cxt_mon.

    (* Imp L *)
    intros Gamma v e A B Delta _ IH1 _ IH2 w HGamma HDelta.
    intros w' ww' H.
    eapply sforces_correct_Imp in H.
    apply H.
    apply wle_refl.
    apply IH2;
      eauto using refutes_cxt_mon,forces_cxt_mon.
    apply wle_refl.
    eauto using forces_mon,refutes_cxt_mon,forces_cxt_mon.

    (* Disjunction L *)
    intros Gamma e1 e2 A1 A2 Delta _ IH1 _ IH2.
    intros w H H0.
    intros w' ww' HDisj.
    apply sforces_correct_Disj in HDisj.
    case HDisj; intro Hcase.
    apply Hcase.
    apply wle_refl.
    apply IH1; eauto using refutes_cxt_mon,forces_cxt_mon.
    apply Hcase.
    apply wle_refl.
    apply IH2; eauto using refutes_cxt_mon,forces_cxt_mon.

    (* Conj LL *)
    intros Gamma e A1 A2 Delta _ IH w H H0.
    intros w' H1 H2.
    apply sforces_correct_Conj in H2.
    destruct H2 as [H2 _].
    apply H2.
    apply wle_refl.
    apply IH; eauto using refutes_cxt_mon,forces_cxt_mon.

    (* Conj LR *)
    intros Gamma e A1 A2 Delta _ IH w H H0.
    intros w' H1 H2.
    apply sforces_correct_Conj in H2.
    destruct H2 as [_ H2].
    apply H2.
    apply wle_refl.
    apply IH; eauto using refutes_cxt_mon,forces_cxt_mon.

    (* Forall L the mirror is easier *)
    intros Gamma e A1 A2 d Hd _ IH w H H0.
    intros w' H1 H2.
    eapply sforces_correct_All in H2.
    apply H2.
    apply wle_refl.
    apply IH; eauto using refutes_cxt_mon,forces_cxt_mon.
    apply wle_refl.
    assumption.

    (* Exists L , hard for similar raesons *)
    intros Gamma e A Delta L Hlocl _ IH w H H0.
    intros w' H1 H2.
    admit.
  Admitted.
End Abstract_Semantics.
