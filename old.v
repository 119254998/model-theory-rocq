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
with term := (* terms in weak PA *)
| t_var : var_term -> term 
| lambda : var_term -> term -> term (* lambda abstraction, which isn't in wpa but is important for the bridge *)
| injl : term -> term (* injection for bridge *)
| injr : term -> term
| paire : term -> term -> term (* pairing for bridge *)
| mu : var_ect -> command -> term (* mu abstraction, still bridge *)
| tall : ect -> term -> term (* universal type forall *)
| texist : ect -> term -> term (* existential type exists *)
with ect := (* e-terms in weak PA *)
| e_var : var_ect -> ect
| app : term -> ect -> ect (* application of term to e-term *)
| disj : ect -> ect -> ect (* disjunction *)
| projl : ect -> ect (* projection left *)
| projr : ect -> ect (* projection right *)
| mu_term : var_term -> command -> ect (* mu abstraction for terms *)
| etall : ect -> ect (* universal term forall *)
| etexist : ect -> ect. (* existential term exists *)

Parameter var_free : Set.
Parameter var_free_dec : forall x y : var_free, {x = y} + {x <> y}. (* decidability of free variable equality *)

Parameters predicate function: Set (* sets of predicate and function symbols *).

Notation "x \notin L" := (In x L -> Empty_set) (at level 70).
Notation "x \in L" := (In x L) (at level 70).

Axiom fresh_free_var : forall L : list var_free, sigT (fun x : var_free => x \notin L).

(*
De Bruijn
*)

Inductive one_term : Set :=
| bound_var : nat -> one_term
| free_var : var_free -> one_term
| func : function -> list one_term -> one_term.

Inductive type : Set :=
| Atomic : predicate -> list one_term -> type
| Imp : type -> type -> type
| Conj : type -> type -> type
| Disj : type -> type -> type
| All : type -> type
| Exi : type -> type.

Fixpoint subst_indiv (n: nat) (a: one_term) (d: one_term) {struct a} : one_term :=
    let subst_list := fix subst_list (l: list one_term) {struct l} : list one_term :=
        match l with
        | nil => nil
        | h :: t => subst_indiv n h d :: subst_list t
        end in 
    match a with
    | func f l => func f (subst_list l)
    | free_var v => free_var v
    | bound_var m => if Nat.eqb n m then d else bound_var m 
    end.
  
Fixpoint subst (n: nat) (A: type) (d: one_term) {struct A} : type := 
  let subst_list := fix subst_list (l: list one_term) {struct l} : list one_term :=
      match l with
      | nil => nil
      | h :: t => subst_indiv n h d :: subst_list t
      end in
      match A with
      | Atomic p l => Atomic p (subst_list l)
      | Imp A1 A2 => Imp (subst n A1 d) (subst n A2 d)
      | Conj A1 A2 => Conj (subst n A1 d) (subst n A2 d)
      | Disj A1 A2 => Disj (subst n A1 d) (subst n A2 d)
      | All A1 => All (subst (S n) A1 d)
      | Exi A1 => Exi (subst (S n) A1 d)
      end.

Notation "A [ n := d ]" := (subst n A d) (at level 20).
Notation "A [ 0 := d ]" := (subst 0 A d) (at level 20).
Notation "A {{ x }}" := (subst 0 A (free_var x)) (at level 20).

(* Notion of bound variables *)