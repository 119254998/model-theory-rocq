From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

(*
The aim is to overload Coq standard library functions
for prop to Type functions
*)

Section Le_Overloaded.
    Inductive le (n:nat): nat -> Set :=
    | le_n: le n n
    | le_S: forall m:nat, le n m -> le n (S m).

    Notation "n <= m" := (le n m) : type_scope.
End Le_Overloaded.

Section In_Overloaded.
    Variable X: Type.
    Open Scope type_scope.

    Fixpoint In (a: X) (l: list X) {struct l} : Set :=
        match l with
        | nil => Empty_set
        | b :: m => (b=a) + In a m
        end.
End In_Overloaded.