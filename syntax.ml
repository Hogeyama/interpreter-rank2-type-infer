type name = string

type ('a, 'b) either = Left of 'a | Right of 'b
type tyvar = TV of (int, string) either
type ty =
  | TyInt
  | TyBool
  | TyVar   of tyvar
  | TyArrow of ty * ty
  | TyPair  of ty * ty
  | TyList  of ty
type type_schema =
  | TsLift   of ty
  | TsForall of tyvar list * type_schema
  | TsArrow  of type_schema * type_schema

type pattern =
  | PInt  of int
  | PBool of bool
  | PVar  of name
  | PPair of pattern * pattern
  | PNil
  | PCons of pattern * pattern

type expr =
  | EConstInt  of int
  | EConstBool of bool
  | EVar       of name
  | EAdd       of expr * expr
  | ESub       of expr * expr
  | EMul       of expr * expr
  | EDiv       of expr * expr
  | EEq        of expr * expr
  | ELt        of expr * expr
  | EIf        of expr * expr * expr
  | EFun       of name * expr
  | EApp       of expr * expr
  | ELet       of (name * expr) list * expr
  | ELetRec    of (name * name * expr) list * expr
  | EPair      of expr * expr
  | ENil
  | ECons      of expr * expr
  | EMatch     of expr * (pattern * expr) list
  | ELetTy     of (name * type_schema * expr) list * expr

type declare =
  | Decl    of (name * expr) list
  | RecDecl of (name * name * expr) list
  (* let (rec) a = ... and b = ... が格納される *)

type command =
  | CExp    of expr
  | CDecl   of declare list
  | CDirect of string * string list

let print_name = print_string

let rec print_pattern p =
  match p with
  | PInt i -> print_int i
  | PBool b -> print_string (string_of_bool b)
  | PVar x -> print_string x
  | PPair (p1, p2) ->
     (print_string "(";
      print_pattern p1;
      print_string ",";
      print_pattern p2;
      print_string ")")
  | PNil -> print_string "[]"
  | PCons (p1, p2) ->
     (print_pattern p1;
      print_string "::";
      print_pattern p2)

(*
 小さい式に対しては以下でも問題はないが，
 大きいサイズの式を見やすく表示したければ，Formatモジュール
   http://caml.inria.fr/pub/docs/manual-ocaml/libref/Format.html
 を活用すること
*)
let rec print_expr e =
  match e with
  | EConstInt i ->
     print_int i
  | EConstBool b ->
     print_string (string_of_bool b)
  | EVar x ->
     print_name x
  | EAdd (e1,e2) ->
     (print_string "EAdd (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")")
  | ESub (e1,e2) ->
     (print_string "ESub (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")")
  | EMul (e1,e2) ->
     (print_string "EMul (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")")
  | EDiv (e1,e2) ->
     (print_string "EDiv (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")")
  | EEq (e1,e2) ->
     (print_string "EEq (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")")
  | ELt (e1, e2) ->
     (print_string "ELt (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")")
  | EIf (e1,e2,e3) ->
     (print_string "EIf (";
      print_expr   e1;
      print_string ",";
      print_expr   e2;
      print_string ",";
      print_expr   e3;
      print_string ")")
  | EFun (x,e) ->
     (print_string ("EFun (" ^ x ^ ",");
      print_expr e;
      print_string ")")
  | EApp (e1,e2) ->
     (print_string "EApp (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")")
  | ELet (l,e1) ->
      let rec f = function
        | [] -> ()
        | (x,e)::l ->
            print_string ("(" ^ x ^ ",");
            print_expr e;
            print_string ")";
            f l in
      print_string "ELetRec (";
      f l;
      print_string ",";
      print_expr e1;
  | ELetRec (l, e1) ->
      let rec g = function
        | [] -> ()
        | (f,x,e)::l ->
            Printf.printf "(%s,%s," f x;
            print_expr e;
            print_string ")";
            g l in
      print_string "ELetRec (";
      g l;
      print_string ",";
      print_expr e1;
  | EPair (e1, e2) ->
      print_string "EPair (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")"
  | ENil ->
     print_string "ENil"
  | ECons (e1, e2) ->
      print_string "ECons (";
      print_expr e1;
      print_string ",";
      print_expr e2;
      print_string ")"
  | EMatch (e, cases) ->
      print_string "EMatch (";
      print_expr e;
      print_string ",";
      print_cases cases;
      print_string ")"
and print_cases cases =
  List.iter (fun (p, e) ->
	     print_pattern p;
	     print_string " -> ";
	     print_expr e;
	     print_string ",")
	    cases

let print_declare : declare -> unit = function
  | Decl l ->
      let rec f = function
        | [] -> ()
        | [(x,e)] ->
            (print_string ("(" ^ x ^ ",");
             print_expr e;
             print_string ")")
        | (x,e)::l ->
            (print_string ("(" ^ x ^ ",");
             print_expr e;
             print_string "), ") in
      print_string "Decl(";
      f l;
      print_string ")"
  | RecDecl l ->
      let rec f = function
        | [] -> ()
        | [(f,x,e)] ->
            (print_string ("(" ^ f ^ "," ^ x ^ ",");
             print_expr e;
             print_string ")")
        | (f,x,e)::l ->
            (print_string ("(" ^ f ^ "," ^ x ^ ",");
             print_expr e;
             print_string "), ") in
      print_string "RecDecl(";
      f l;
      print_string ")"

let rec print_command p =
  match p with
  | CExp e -> print_expr e
  | CDecl declist ->
      let rec f = function
        | [] -> ()
        | dec::l ->
            print_declare dec;
            print_newline ();
            f l in
      f declist
  | CDirect (s,l) -> Printf.printf "CDirect %s" s


