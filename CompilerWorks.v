From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

(* Transformer: switches b/w dialects, prove rel is involution. *)
(* Optimization: remove unused tables from FROM/JOIN clauses. *)

Local Open Scope string_scope.

Definition relation : Type := (list string) * list (string -> string).

Inductive jclause : Type :=
| LeftJoin (rel : relation) (onlhs : string) (onrhs : string).

Inductive wclause : Type :=
| WhereEqual (fld : string) (val : string).

Inductive sqlstmt : Type :=
| Select (flds: list string) (rel: relation)
         (join: option jclause)
         (wheres: option (list wclause)).

Definition fruits : relation :=
  (["id" ; "name" ; "price"] ,
   [fun c => match c with "id"=>"1"|"name"=>"orange"|"price"=>"5"|_=>"" end ;
    fun c => match c with "id"=>"2"|"name"=>"apple"|"price"=>"9"|_=>"" end ;
    fun c => match c with "id"=>"3"|"name"=>"banana"|"price"=>"5"|_=>"" end ;
    fun c => match c with "id"=>"4"|"name"=>"kiwi"|"price"=>"8"|_=>"" end]).

Definition render (rel : relation) :=
    let fix render_aux (flds : list string) (rows : list (string -> string)) :=
      match flds, rows with
      | fs, r::rs =>
        (map (fun f => (r f)) fs) :: (render_aux fs rs)
      | _, _ => []
      end
    in (fst rel) :: render_aux (fst rel) (snd rel).

Example ex1 : render fruits =
              [["id" ; "name" ; "price"] ;
               ["1" ; "orange" ; "5"] ;
               ["2" ; "apple" ; "9"] ;
               ["3" ; "banana" ; "5"] ;
               ["4" ; "kiwi" ; "8"]].
Proof. unfold render. simpl. reflexivity. Qed.

(*
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
 *)

 (* Old wheres: | whd::wtl => eval flds (evalwhere whd rel) wtl *)
Definition evalstmt (stmt : sqlstmt) : relation :=
  let fix select_fields (flds : list string) (row : (string -> string))
                        : (string -> string) :=
    match flds with
    | f::fs => (fun c => if (string_dec c f)
                        then (row c) else ((select_fields fs) row) c)
    | [] => (fun _ => "")
    end
  in 
  match stmt with
  | Select fields rel None _  => (fields, (map (select_fields fields) (snd rel)))
  | Select fields rel (Some (LeftJoin reljoin fld_l fld_r)) _  =>
    let fix ljoin (rows_r : list (string -> string)) (row_l : (string -> string))
                  : list (string -> string) :=
        match rows_r with
        | row_r::rs =>
            if string_dec (row_l fld_l) (row_r fld_r) then
              (fun c => let a := (row_l c) in
                        if (string_dec a "") then (row_r c) else a)
                :: (ljoin rs row_l)
            else (ljoin rs row_l)
        | [] => []
        end
    in
    (* This is a left join; if right relation has no records, return left as is. *)
    match (snd rel) with
    | _::_ =>  (fields, (map (select_fields fields)
                 (flat_map (fun row_l => ljoin (snd reljoin) (row_l)) (snd rel))))
    | [] => (fields, (map (select_fields fields) (snd rel)))
    end
  end.

Example ex2 : (render (evalstmt (Select ["name"] fruits None None)))
              = [["name"] ; ["orange"] ; ["apple"] ; ["banana"] ; ["kiwi"] ].
Proof. unfold render. simpl. reflexivity. Qed. 

Example ex3 : (render (evalstmt (Select ["id";"name"] fruits None None)))
              = [["id";"name"] ; ["1";"orange"] ; ["2";"apple"] ;
                   ["3";"banana"] ; ["4";"kiwi"] ].
Proof. simpl. reflexivity. Qed.

Example ex4 : (render (evalstmt (Select ["name" ; "id"] fruits None None)))
              = [["name";"id"] ; ["orange";"1"] ; ["apple";"2"] ; ["banana";"3"] ; ["kiwi";"4"] ].
Proof. unfold render. simpl. reflexivity. Qed.

(*
Example ex5 : (render (evalstmt (SelectWhere ["id";"name"] fruits [(WhereEqual "name" "kiwi")])))
              = [ ["4";"kiwi"] ].
Proof. unfold render; simpl.

       reflexivity. Qed.

Example ex6 : (eval ["name"] fruits [(WhereEqual "price" "5")])
              = [ ["orange"] ; ["banana"]].
Proof. simpl. reflexivity. Qed.

Example ex7 : (eval ["name"] fruits [(WhereEqual "price" "5");(WhereEqual "id" "3")])
              = [ ["banana"]].
Proof. simpl. reflexivity. Qed.
 *)

Example ex6_subquery :
  (render (evalstmt (Select ["name"]
           (evalstmt (Select ["price";"name"] fruits None None)) None None)))
              = [["name"] ; ["orange"] ; ["apple"] ; ["banana"] ; ["kiwi"] ].
Proof. unfold render. simpl. reflexivity. Qed.

Definition stores : relation :=
  (["sid";"sname";"sfruit"] ,
  [fun c => match c with "sid"=>"1"|"sname"=>"La Tienda"|"sfruit"=>"4"|_=>"" end ;
   fun c => match c with "sid"=>"2"|"sname"=>"Duka 88"|"sfruit"=>"1"|_=>"" end]).

(* TODO: Define a join evaluator that can combine two relations. I envision
   this is a destructuring of each (string -> string) such that the join
   column is deduplicated and the entire record itself is only present if
   the value in the left relation matches that of the right. The important part
   is that the evaluator shouldn't return lists of strings, it should return
   proper relations. A separate function (i.e., "render") should "evaluate" the
   relation itself into actual lists so that we can write proofs about it.
 *)


Example ex7_join1 : (render (evalstmt (Select ["sname" ; "name"] stores
                                        (Some (LeftJoin fruits "sfruit" "id")) None)))
              = [["sname";"name"];["La Tienda";"kiwi"];["Duka 88";"orange"]].
Proof. unfold render. simpl. reflexivity. Qed.