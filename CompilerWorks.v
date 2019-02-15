From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Local Open Scope string_scope.

(*
Inductive fld : Type :=
| StrF : string -> fld
| NatF : nat -> fld.

Inductive row : Type :=
| Row : (string -> fld) -> row.

Inductive relation : Type :=
| Rel (rows: list row).

Inductive fromclause : Type :=
| From (rel: relation).
*)
Inductive stmt : Type :=
| Select (fld: string).

(* Transformer: switches b/w dialects, prove rel is involution. *)
(* Optimization: remove unused tables from FROM/JOIN clauses. *)

Definition fruits : list (string -> string) := [
    fun col => if string_dec col "id" then "1" else "orange" ;
    fun col => if string_dec col "id" then "2" else "apple" ;                              fun col => if string_dec col "id" then "3" else "banana" ;
    fun col => if string_dec col "id" then "4" else "kiwi"].

Example ex1 : map (fun r => (r "name")) fruits
               = ["orange" ; "apple" ; "banana" ; "kiwi"].
Proof. reflexivity. Qed.

Definition q1 : stmt := (Select "name").

Fixpoint eval (flds : list string) (rel: list (string->string)) :=
  map (fun r => (map (fun f => (r f)) flds)) rel.

Example ex2 : (eval ["name"] fruits)
              = [["orange"] ; ["apple"] ; ["banana"] ; ["kiwi"] ].
Proof. simpl. reflexivity. Qed.

Example ex3 : (eval ["id";"name"] fruits)
              = [["1";"orange"] ; ["2";"apple"] ; ["3";"banana"] ; ["4";"kiwi"] ].
Proof. simpl. reflexivity. Qed.

Example ex4 : (eval ["name";"id"] fruits)
              = [["orange";"1"] ; ["apple";"2"] ; ["banana";"3"] ; ["kiwi";"4"] ].
Proof. simpl. reflexivity. Qed.


