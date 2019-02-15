From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Inductive stmt : Type :=
| Select (fld: string).

Inductive wclause : Type :=
| WhereEqual (fld : string) (val : string).

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

Fixpoint evalwhere (w : wclause) (rel : list (string -> string)) :=
  match w with
  | WhereEqual wfld wval =>
    match rel with
    | hrow::tlrows =>
      if string_dec (hrow wfld) wval then hrow :: (evalwhere w tlrows)
                                     else         (evalwhere w tlrows)
    | _ => []
    end
  end.

Fixpoint eval (flds : list string) (rel: list (string->string))
              (wheres : list wclause) :=
  match wheres with
  | whd::wtl => eval flds (evalwhere whd rel) wtl
  | [] => map (fun r => (map (fun f => (r f)) flds)) rel
  end.

Example ex2 : (eval ["name"] fruits [])
              = [["orange"] ; ["apple"] ; ["banana"] ; ["kiwi"] ].
Proof. simpl. reflexivity. Qed.

Example ex3 : (eval ["id";"name"] fruits [])
              = [["1";"orange"] ; ["2";"apple"] ; ["3";"banana"] ; ["4";"kiwi"] ].
Proof. simpl. reflexivity. Qed.

Example ex4 : (eval ["name";"id"] fruits [])
              = [["orange";"1"] ; ["apple";"2"] ; ["banana";"3"] ; ["kiwi";"4"] ].
Proof. simpl. reflexivity. Qed.

Example ex5 : (eval ["id";"name"] fruits [(WhereEqual "name" "kiwi")])
              = [ ["4";"kiwi"] ].
Proof. simpl. reflexivity. Qed.

