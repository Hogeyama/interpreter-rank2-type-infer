
open Syntax
open Typecheck

let debug_mode = false

(*{{{ type declare *)
exception Unify of string
exception TypeError of string

type name = string
(* \Lambda^{-,*} *)
type expr_star =
  | ESConstInt  of int
  | ESConstBool of bool
  | ESVar       of name * int option (* label *)
  | ESAdd       of expr_star  * expr_star
  | ESSub       of expr_star  * expr_star
  | ESMul       of expr_star  * expr_star
  | ESDiv       of expr_star  * expr_star
  | ESEq        of expr_star  * expr_star
  | ESLt        of expr_star  * expr_star
  | ESIf        of expr_star  * expr_star * expr_star
  | ESApp       of expr_star  * expr_star
  | ESAbs       of int * name * expr_star

type theta_nf = {
    xs : name list;      (* x0, ..., x(m-1) *)
    ys : name list;      (* y0, ..., y(n-1) *)
    es : expr_star list; (* t0, ..., t(n-1), tn *)
  }
(* 次の式を表す:
 * \x0.\x1. ... \x(m-1). let y0 = t0 in let y1 = t1 in ... let y(n-1) = t(n-1) in tn *)


type ineq = ty * ty
type asup = ineq list

type path = lr list
and  lr = L | R

type subst = (tyvar * ty) list
type ('a, 'b) either = Left of 'a | Right of 'b

let rec nub = function
  | [] -> []
  | x::xs -> x :: nub (List.filter (fun y -> x <> y) xs)

exception Unification of string
(*}}}*)

(*{{{ 便利関数 *)
let rec take n l =
  if n<1 then [] else
  match n,l with
    | _, [] -> []
    | 1, (x::_)  -> [x]
    | _, (x::xs) -> x :: take (n-1) xs

let is_substring s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

let rec int_list n m = (* [n;...;m] *)
  if n>m
    then []
    else n::int_list (n+1) m

let find_first_index x xs =
  let ys = List.combine xs (int_list 0 (List.length xs - 1)) in
  List.assoc x ys

let find_last_index x xs =
  let ys = List.combine xs (int_list 0 (List.length xs - 1)) in
  List.assoc x (List.rev ys)

let sprintf = Printf.sprintf

let name_cnt = ref 0
let new_name () = name_cnt := !name_cnt+1; ("_x"^string_of_int !name_cnt)

let undefined() = failwith "undefined"

module StrMap = Map.Make(String)

(*}}}*)

(*{{{ type 便利関数 *)
(* get_type_vars *)
let rec get_type_vars : ty -> tyvar list =(*{{{*)
  fun ty ->
    let s = ref ([] : tyvar list) in
    let rec f =
      function
      | TyVar a when List.mem a !s -> ()
      | TyVar a                    -> s := a :: !s
      | TyArrow (tau1,tau2) ->
          f tau1; f tau2
      | TyInt
      | TyBool -> () in
    ignore (f ty); !s
(*}}}*)
let rec get_type_vars_tyschm : type_schema -> tyvar list = (*{{{*)
  function
    | TsLift tau -> get_type_vars tau
    | TsForall(_,sigma) -> get_type_vars_tyschm sigma
    | TsArrow(sigma1, sigma2) -> nub (get_type_vars_tyschm sigma1 @ get_type_vars_tyschm sigma2)
(*}}}*)

(* subst系 *)
let rec expr_subst : expr -> name -> expr -> expr = (*{{{*)
(* e1[x:=e2] *)
  fun e1 x e2 -> match e1 with
  | EVar y when x=y -> e2
  | EVar _ -> e1

  | EFun (y, e11) when x<>y ->
      EFun (y, expr_subst e11 x e2)
  | EFun _ -> e1

  | EApp (e11, e12) ->
      EApp (expr_subst e11 x e2, expr_subst e12 x e2)

  | EAdd (e11,e12) ->
      EAdd (expr_subst e11 x e2, expr_subst e12 x e2)
  | ESub (e11,e12) ->
      ESub (expr_subst e11 x e2, expr_subst e12 x e2)
  | EMul (e11,e12) ->
      EMul (expr_subst e11 x e2, expr_subst e12 x e2)
  | EDiv (e11,e12) ->
      EDiv (expr_subst e11 x e2, expr_subst e12 x e2)
  | EEq  (e11,e12) ->
      EEq  (expr_subst e11 x e2, expr_subst e12 x e2)
  | ELt  (e11,e12) ->
      ELt  (expr_subst e11 x e2, expr_subst e12 x e2)
  | EIf (e11,e12,e13) ->
      EIf (expr_subst e11 x e2, expr_subst e12 x e2, expr_subst e13 x e2)

  | EConstInt _
  | EConstBool _ -> e1

  | ELet (y,e11,e12) when y=x ->
      ELet (y, expr_subst e11 x e2, e12)
  | ELet (y,e11,e12) ->
      ELet (y, expr_subst e11 x e2, expr_subst e12 x e2)
  | ELetRec (f,y,e11,e12) when x=y ->
      ELetRec (f,y,e11, expr_subst e12 x e2)
  | ELetRec (f,y,e11,e12) when x=f ->
      e1
  | ELetRec (f,y,e11,e12) ->
      ELetRec (f,y, expr_subst e11 x e2, expr_subst e12 x e2)
  | EMacro (y,e11,e12) when y=x ->
      EMacro (y, expr_subst e11 x e2, e12)
  | EMacro (y,e11,e12) ->
      EMacro (y, expr_subst e11 x e2, expr_subst e12 x e2)
(*}}}*)
let rec rm_macro : expr -> expr = (*{{{*)
  fun e -> match e with
  | EMacro (x,e1,e2) -> rm_macro (expr_subst e2 x e1)
  | EConstInt _ 
  | EConstBool _
  | EVar _ -> e
  | ELet (x,e1,e2) -> ELet (x, rm_macro e1, rm_macro e2)
  | ELetRec (f,x,e1,e2) -> ELetRec (f,x, rm_macro e1, rm_macro e2)
  | EFun (x, e1) -> EFun (x, rm_macro e1)
  | EApp (e1,e2) -> EApp (rm_macro e1, rm_macro e2)
  | EAdd (e1,e2) -> EAdd (rm_macro e1, rm_macro e2)
  | ESub (e1,e2) -> ESub (rm_macro e1, rm_macro e2)
  | EMul (e1,e2) -> EMul (rm_macro e1, rm_macro e2)
  | EDiv (e1,e2) -> EDiv (rm_macro e1, rm_macro e2)
  | EEq  (e1,e2) -> EEq  (rm_macro e1, rm_macro e2)
  | ELt  (e1,e2) -> ELt  (rm_macro e1, rm_macro e2)
  | EIf  (e1,e2,e3) ->
      EIf  (rm_macro e1, rm_macro e2, rm_macro e3)
(*}}}*)
let rec expr_star_subst : expr_star -> name -> expr_star -> expr_star = (*{{{*)
(* e1[x:=e2] *)
  fun e1 x e2 -> match e1 with
  | ESVar (y,_) when x=y -> e2
  | ESVar _ -> e1

  | ESAbs (i, y, e11) when x<>y ->
      ESAbs (i, y, expr_star_subst e11 x e2)
  | ESAbs _ -> e1

  | ESApp (e11, e12) ->
      ESApp (expr_star_subst e11 x e2, expr_star_subst e12 x e2)

  | ESAdd (e11,e12) ->
      ESAdd (expr_star_subst e11 x e2, expr_star_subst e12 x e2)
  | ESSub (e11,e12) ->
      ESSub (expr_star_subst e11 x e2, expr_star_subst e12 x e2)
  | ESMul (e11,e12) ->
      ESMul (expr_star_subst e11 x e2, expr_star_subst e12 x e2)
  | ESDiv (e11,e12) ->
      ESDiv (expr_star_subst e11 x e2, expr_star_subst e12 x e2)
  | ESEq  (e11,e12) ->
      ESEq  (expr_star_subst e11 x e2, expr_star_subst e12 x e2)
  | ESLt  (e11,e12) ->
      ESLt  (expr_star_subst e11 x e2, expr_star_subst e12 x e2)
  | ESIf (e11,e12,e13) ->
      ESIf (expr_star_subst e11 x e2, expr_star_subst e12 x e2, expr_star_subst e13 x e2)
  | ESConstInt _
  | ESConstBool _ -> e1
(*}}}*)
let asup_subst : subst -> asup -> asup = (*{{{*)
  fun sbst asup ->
    let f (t1,t2) = (ty_subst sbst t1, ty_subst sbst t2) in
    List.map f asup
(*}}}*)
let fleshize : ty -> ty =(*{{{*)
  fun ty ->
    let tvs = get_type_vars ty in
    let f tv =
      let tv' = new_var() in
      (tv, TyVar tv') in
    let sbst = List.map f tvs in
    ty_subst sbst ty
(*}}}*)

let rec print_expr_star e = (*{{{*)
  match e with
  | ESConstInt i ->
      print_int i
  | ESConstBool b ->
      print_string (string_of_bool b)
  | ESVar (x, Some i) ->
      print_name x; print_string "-";print_int i;
  | ESVar (x, None) ->
      print_name x
  | ESAdd (e1,e2) ->
     (print_string "ESAdd (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ")")
  | ESSub (e1,e2) ->
     (print_string "ESSub (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ")")
  | ESMul (e1,e2) ->
     (print_string "ESMul (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ")")
  | ESDiv (e1,e2) ->
     (print_string "ESDiv (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ")")
  | ESEq (e1,e2) ->
     (print_string "ESESq (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ")")
  | ESLt (e1, e2) ->
     (print_string "ESLt (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ")")
  | ESIf (e1,e2,e3) ->
     (print_string "ESIf (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ",";
      print_expr_star e3;
      print_string ")")
  | ESAbs (i,x,e) ->
     (print_string ("ESAbs (" ^ x ^ "-" ^ string_of_int i ^",");
      print_expr_star e;
      print_string ")")
  | ESApp (e1,e2) ->
     (print_string "ESApp (";
      print_expr_star e1;
      print_string ",";
      print_expr_star e2;
      print_string ")")
let print_ineq (t1,t2)=
  Printf.printf "(%s,%s)\n" (show_ty_debug t1) (show_ty_debug t2)
(*}}}*)
(*}}}*)

(* System Λ_2^- -> System Λ_2^{-,*} *)
let rec act : expr -> name list =(*{{{*)
  function
  | EVar _ -> []
  | EFun (x, e) -> x::act e
  | EApp (e1, e2) ->
      (match act e1 with
        | [] -> []
        | x::l -> l)
  | ELet (_,_,e2) -> act e2
  | _ -> []
(*}}}*)
let rec label_sub : expr -> name list -> int -> int StrMap.t -> expr_star =(*{{{*)
(*不安あり dicの扱い合ってるのかしら*)
  fun e xs i dic -> match e with
  | EVar x ->
      (try
        let i = StrMap.find x dic in
        ESVar(x,Some i)
      with
        Not_found -> ESVar(x, None))
  | EFun(x, e1) when List.mem x xs -> ESAbs (i, x, label_sub e1 xs i (StrMap.add x i dic))
  | EFun(x, e1)                    -> ESAbs (1, x, label_sub e1 xs i (StrMap.add x 1 dic))
  | EApp(e1,e2) -> ESApp(label_sub e1 xs i dic, label_sub e2 (act e2) 3 dic)
  | EAdd(e1,e2) -> ESAdd(label_sub e1 xs i dic, label_sub e2 xs i dic)
  | ESub(e1,e2) -> ESSub(label_sub e1 xs i dic, label_sub e2 xs i dic)
  | EMul(e1,e2) -> ESMul(label_sub e1 xs i dic, label_sub e2 xs i dic)
  | EDiv(e1,e2) -> ESDiv(label_sub e1 xs i dic, label_sub e2 xs i dic)
  | EEq (e1,e2) -> ESEq (label_sub e1 xs i dic, label_sub e2 xs i dic)
  | ELt (e1,e2) -> ESLt (label_sub e1 xs i dic, label_sub e2 xs i dic)
  | EIf (e1,e2,e3) -> ESIf (label_sub e1 xs i dic
                           ,label_sub e2 xs i dic
                           ,label_sub e3 xs i dic)
  | ELet(x,e1,e2) ->
      let e1' = label_sub e1 (act e1) 3 dic in
      let e2' = label_sub e2 xs       i (StrMap.add x 1 dic) in
      ESApp(ESAbs(1, x, e2'), e1')
  | EConstInt n -> ESConstInt n
  | EConstBool b -> ESConstBool b
  | _ -> failwith ("This expression requires at least rank 2 polymorphic type but \n" ^
                   "rank 2 type inferrence is not implemented for this type of expression")
(*}}}*)
let label : expr -> expr_star =(*{{{*)
  fun e -> label_sub e (act e) 2 StrMap.empty
(*}}}*)


(* System Λ_2^{-,*} -> theta_nf *)
let rec has_theta_redex : expr_star -> bool = (*{{{*)
  fun e -> match e with
  | ESApp(ESApp (ESAbs (1, _, _), _), _)
  | ESAbs(3, _, ESApp(ESAbs(1, _, _), _))
  | ESApp(_, (ESApp(ESAbs(1,_,_), _)))
  | ESApp(ESAbs(1,_,(ESAbs(2,_,_))), _) -> true

  | ESAbs (_,_,e1) -> has_theta_redex e1

  | ESApp (e1,e2)
  | ESAdd (e1,e2)
  | ESSub (e1,e2)
  | ESMul (e1,e2)
  | ESDiv (e1,e2)
  | ESEq  (e1,e2)
  | ESLt  (e1,e2) -> has_theta_redex e1 || has_theta_redex e2

  | ESIf (e1,e2,e3) -> has_theta_redex e1 || has_theta_redex e2 || has_theta_redex e3

  | ESVar _
  | ESConstInt _
  | ESConstBool _ -> false
(*}}}*)
let rec is_theta_redex : expr_star -> bool = (*{{{*)
  fun e -> match e with
  | ESApp(ESApp (ESAbs (1, _, _), _), _)
  | ESAbs(3, _, ESApp(ESAbs(1, _, _), _))
  | ESApp(_, (ESApp(ESAbs(1,_,_), _)))
  | ESApp(ESAbs(1,_,(ESAbs(2,_,_))), _) -> true
  | _ -> false
  (* これで十分 *)
(*}}}*)
let obviously_has_no_theta_redex : expr_star -> bool =(*{{{*)
  function
  | ESVar _
  | ESApp (ESVar _, ESVar _) -> true
  | _ -> false
  (* ESAdd(e1,e2)とかで e1 = ESApp (ESVar _, ESVar _) のときに
   * e1を変数で置いちゃう[1]と theta2-reduce と合わせて無限ループに入る.
   *  [1]: e1+e2 を let x = e1 in x+e2 にすること
   *)
(*}}}*)
let rec theta_nf_sub : expr_star -> expr_star = (*{{{*)
  (* TODO 停止性を考える (任意の標準形に対して停止することが言えればok) *)
  let p = obviously_has_no_theta_redex in
  fun e -> match e with
  | ESApp (ESApp (ESAbs (1, x, e1), e2), e3) ->
      (*print_endline "theta1";*)
      theta_nf_sub (ESApp(ESAbs(1, x, ESApp(e1,e3)), e2))

  | ESAbs(3, x, ESApp(ESAbs(1, y, e1), e2)) ->
      (*print_endline "theta2";*)
      let v = new_name() in
      let w = new_name() in
      let ne1 = ESAbs(1, v,
                  ESAbs(3, x,
                    expr_star_subst e1 y (ESApp(ESVar(v, Some 1), ESVar(x, Some 3))))) in
      let ne2 = ESAbs(3, w,
                  expr_star_subst e2 x (ESVar(w, Some 3))) in
      theta_nf_sub (ESApp(ne1, ne2))

  | ESApp(e1, (ESApp(ESAbs(1,x,e2), e3))) ->
      (*print_endline "theta3";*)
      theta_nf_sub (ESApp(ESAbs(1,x,ESApp(e1,e2)), e3))

  | ESApp(ESAbs(1,x,(ESAbs(2,y,e1))), e2) ->
      (*print_endline "theta4";*)
      theta_nf_sub (ESAbs(2,y,ESApp(ESAbs(1,x,e1), e2)))

  | ESApp (e1, e2) ->
      let e' = (ESApp(theta_nf_sub e1, theta_nf_sub e2)) in
      if is_theta_redex e' then theta_nf_sub e' else e'

  | ESAbs (i, x, e1) ->
      assert(List.mem i [1;2;3]);
      let e' = (ESAbs(i, x, theta_nf_sub e1)) in
      if is_theta_redex e' then theta_nf_sub e' else e'
      (*if false then theta_nf_sub e' else e'*)
  | ESAdd(e1,e2) when p e1 && p e2 ->
      e
  | ESAdd(e1,e2) when p e1 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESAdd(e1, ESVar(y, Some 1))), e2))
  | ESAdd(e1,e2) when p e2 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESAdd(ESVar(y, Some 1), e2)), e1))
  | ESAdd(e1,e2) ->
      let x = new_name() in
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1,x,
                      (ESApp(ESAbs(1,y,
                          ESAdd(ESVar(x, Some 1), ESVar(y, Some 1))),
                      e2))),
                   e1))

  | ESSub(e1,e2) when p e1 && p e2 ->
      e
  | ESSub(e1,e2) when p e1 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESSub(e1, ESVar(y, Some 1))), e2))
  | ESSub(e1,e2) when p e2 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESSub(ESVar(y, Some 1), e2)), e1))
  | ESSub(e1,e2) ->
      let x = new_name() in
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1,x,
                       (ESApp(ESAbs(1,y,
                           ESSub(ESVar(x, Some 1), ESVar(y, Some 1))),
                       e2))),
                   e1))
  | ESMul(e1,e2) when p e1 && p e2 ->
      e
  | ESMul(e1,e2) when p e1 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESMul(e1, ESVar(y, Some 1))), e2))
  | ESMul(e1,e2) when p e2 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESMul(ESVar(y, Some 1), e2)), e1))
  | ESMul(e1,e2) ->
      let x = new_name() in
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1,x,
                       (ESApp(ESAbs(1,y,
                           ESMul(ESVar(x, Some 1), ESVar(y, Some 1))),
                       e2))),
                   e1))
  | ESDiv(e1,e2) when p e1 && p e2 ->
      e
  | ESDiv(e1,e2) when p e1 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESDiv(e1, ESVar(y, Some 1))), e2))
  | ESDiv(e1,e2) when p e2 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESDiv(ESVar(y, Some 1), e2)), e1))
  | ESDiv(e1,e2) ->
      let x = new_name() in
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1,x,
                       (ESApp(ESAbs(1,y,
                           ESDiv(ESVar(x, Some 1), ESVar(y, Some 1))),
                       e2))),
                   e1))
  | ESEq (e1,e2) when p e1 && p e2 ->
      e
  | ESEq (e1,e2) when p e1 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESEq (e1, ESVar(y, Some 1))), e2))
  | ESEq (e1,e2) when p e2 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESEq (ESVar(y, Some 1), e2)), e1))
  | ESEq (e1,e2) ->
      let x = new_name() in
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1,x,
                       (ESApp(ESAbs(1,y,
                           ESEq (ESVar(x, Some 1), ESVar(y, Some 1))),
                       e2))),
                   e1))
  | ESLt (e1,e2) when p e1 && p e2 ->
      e
  | ESLt (e1,e2) when p e1 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESLt (e1, ESVar(y, Some 1))), e2))
  | ESLt (e1,e2) when p e2 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESLt (ESVar(y, Some 1), e2)), e1))
  | ESLt (e1,e2) ->
      let x = new_name() in
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1,x,
                       (ESApp(ESAbs(1,y,
                           ESLt (ESVar(x, Some 1), ESVar(y, Some 1))),
                       e2))),
                   e1))
  | ESIf (e1,e2,e3) when p e1 && p e2 && p e3 ->
      e
  | ESIf (e1,e2,e3) when p e1 && p e2 ->
      let z = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, z, ESIf(e1, e2, ESVar(z, Some 1))), e3))
  | ESIf (e1,e2,e3) when p e2 && p e3 ->
      let x = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, x, ESIf(ESVar(x, Some 1), e2, e3)), e1))
  | ESIf (e1,e2,e3) when p e1 && p e3 ->
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y, ESIf(e1, ESVar(y, Some 1), e3)), e2))
  | ESIf (e1,e2,e3) when p e1 ->
      let y = new_name() in
      let z = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, y,
                      ESApp(ESAbs(1, z,
                        ESIf(e1, ESVar(y, Some 1), (ESVar(z, Some 1)))),
                      e3)),
                    e2))
  | ESIf (e1,e2,e3) when p e2 ->
      let x = new_name() in
      let z = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, x,
                      ESApp(ESAbs(1, z,
                        ESIf(ESVar(x, Some 1), e2, (ESVar(z, Some 1)))),
                      e3)),
                    e1))
  | ESIf (e1,e2,e3) when p e3 ->
      let x = new_name() in
      let y = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, x,
                      ESApp(ESAbs(1, y,
                        ESIf(ESVar(x, Some 1), (ESVar(y, Some 1)), e3)),
                      e2)),
                    e1))
  | ESIf (e1,e2,e3) ->
      let x = new_name() in
      let y = new_name() in
      let z = new_name() in
      theta_nf_sub (ESApp(ESAbs(1, x,
                     ESApp(ESAbs(1, y,
                       ESApp(ESAbs(1, z,
                         ESIf(ESVar(x, Some 1), (ESVar(y, Some 1)), (ESVar(z, Some 1)))),
                       e3)),
                     e2)),
                   e1))

  | ESConstInt  _
  | ESConstBool _
  | ESVar       _ -> e
(*}}}*)
let theta_nf : expr_star -> theta_nf =(*{{{*)
  fun e ->
    let e1 = theta_nf_sub e in
    let (xs, e2) =
      let rec f xs e1 =
        match e1 with
        | ESAbs(2, x, e1') -> f (x::xs) e1'
        | _ -> (xs, e1)
      in f [] e1 in
    let (ys, es, e3) =
      let rec f ys es e2 =
        match e2 with
        | ESApp(ESAbs(1, y, e21), e22) -> f (y::ys) (e22::es) e21
        | _ -> (ys,es,e2) in
      f [] [] e2 in
    { xs = List.rev xs
    ; ys = List.rev ys
    ; es = List.rev (e3::es)
    }
(*}}}*)


(*  theta_nf -> ASUP *)
let (=:=) tau1 tau2 : ineq =(*{{{*)
  let alpha = TyVar(new_var()) in
  ((TyArrow(alpha,alpha)),(TyArrow(tau1,tau2)))
(*}}}*)
(*{{{ log for debug *)
let tylog   : (expr_star   * ty) list ref = ref []
let betalog : ((int * int) * ty) list ref = ref []
let tylog_write   e ty   = tylog   := (e,ty)    :: !tylog
let betalog_write i j ty = betalog := ((i,j),ty):: !betalog
(*}}}*)
let rec instantiate : type_schema -> ty = (*{{{*)
  fun sigma ->
    let rec is_quaunified : type_schema -> bool =
      function
        | TsLift _ -> false
        | TsForall([], sigma) -> is_quaunified sigma
        | TsForall(l, _) -> true
        | TsArrow(sigma1,sigma2) -> is_quaunified sigma1 || is_quaunified sigma2 in
    match sigma with
      | TsLift tau -> tau
      | TsForall([], sigma1) ->
          instantiate sigma1
      | TsForall(l, sigma1) when is_quaunified sigma1 ->
          failwith "rank 3 required"
      | TsForall(l, sigma1) ->
          let tau = instantiate sigma1 in
          let f tv =
            let tv' = new_var()
            in (tv, TyVar tv') in
          let sbst = List.map f l in
          ty_subst sbst tau
      | TsArrow(sigma1, sigma2) when is_quaunified sigma ->
          failwith "rank 3 required"
      | TsArrow(sigma1, sigma2) ->
          let tau1 = instantiate sigma1 in
          let tau2 = instantiate sigma2 in
          TyArrow(tau1,tau2)
(*}}}*)
let asup_of_theta_nf : tyenv -> theta_nf -> ty * asup = (*{{{*)
  fun tyenv {xs;ys;es} ->
    (*let m = List.length xs in*)
    let n = List.length ys in
    let beta : ty array array =
      let new_tyvar' n = TyVar(new_var ()) in
      let betaj j = Array.init (n+1-j) new_tyvar' in
      Array.init n betaj in
    let beta i j : ty =
      (* beta i j = yj の ei 中の型みたいな気持ち. ただしbeta j jはyjの一般的な型
       * jの範囲は 0~n-1
       * iの範囲は j~n  *)
      beta.(j).(i-j) in

    for j = 0 to n-1 do
      for i = j to n do
         betalog_write i j (beta i j)
      done
    done;

    let asup_ref = ref [] in
    let add_ineq ty1 ty2 =
      asup_ref := (ty1,ty2) :: !asup_ref in
    let add_eq ty1 ty2 =
      asup_ref := (ty1=:=ty2) :: !asup_ref in
    let ty_en = ref TyInt in
    for i = 0 to n do
      let ei = List.nth es i in
      let rec f zts e =
        (*print_expr_star e;*)
        match e with
        | ESVar(y,Some 1) ->
            let ty_e = TyVar(new_var ()) in
            let j = find_last_index y ys in
            add_ineq (beta i j) ty_e;
            tylog_write e ty_e;
            ty_e
        | ESVar(_,Some 2) ->
            let ty_e = TyVar(new_var ()) in
            tylog_write e ty_e;
            ty_e
        | ESVar(z,Some 3) ->
            let ty_e = TyVar(new_var ()) in
            let ty_z = List.assoc z zts in
            add_eq ty_z ty_e;
            tylog_write e ty_e;
            ty_e
        | ESVar(w, None) ->
            (try
              instantiate (List.assoc w tyenv)
             with Not_found -> failwith ("infer_expr: '" ^ w ^ "' Not_found"))
        | ESAbs(3,z,e1) ->
            let ty_e  = TyVar(new_var ()) in
            let ty_z  = TyVar(new_var ()) in
            let ty_e1 = f ((z,ty_z)::zts) e1 in
            add_eq ty_e (TyArrow(ty_z,ty_e1));
            tylog_write e ty_e;
            ty_e
        | ESApp(e1,e2) ->
            let ty_e  = TyVar(new_var ()) in
            let ty_e1 = f zts e1 in
            let ty_e2 = f zts e2 in
            add_eq ty_e1 (TyArrow(ty_e2, ty_e));
            tylog_write e ty_e;
            ty_e
        | ESAdd(e1,e2)
        | ESSub(e1,e2)
        | ESMul(e1,e2)
        | ESDiv(e1,e2) -> (* TODO ほんとに? *)
            let ty_e1 = f zts e1 in
            let ty_e2 = f zts e2 in
            add_eq ty_e1 TyInt;
            add_eq ty_e2 TyInt;
            tylog_write e TyInt;
            TyInt
        | ESEq(e1,e2)
        | ESLt(e1,e2) ->
            let ty_e1 = f zts e1 in
            let ty_e2 = f zts e2 in
            let ty  = TyVar(new_var ()) in
            add_ineq ty_e1 ty;
            add_ineq ty_e2 ty;
            tylog_write e TyBool;
            TyBool
        | ESIf(e1,e2,e3) ->
            let ty_e1 = f zts e1 in
            let ty_e2 = f zts e2 in
            let ty_e3 = f zts e3 in
            let ty  = TyVar(new_var ()) in
            add_ineq ty_e1 TyBool;
            add_ineq ty_e2 ty;
            add_ineq ty_e3 ty;
            tylog_write e ty;
            ty

        | ESConstInt  _ -> TyInt
        | ESConstBool _ -> TyBool

        | ESAbs _ -> (*raise (Unify "rank3 required") *)
            print_string "rank3 may be required\n"; assert false
        | ESVar(_,Some _) -> print_expr_star e; assert false in
      let ty_ei = (f [] ei) in
      if i <> n
        then add_eq (beta i i) ty_ei
        else ty_en := ty_ei
    done;
    for j = 0 to n-1 do
      for i = j+1 to n do
        add_ineq (beta (i-1) j) (beta i j)
      done
    done;
    (!ty_en, !asup_ref)
(*}}}*)


(* solve ASUP *)
let rec search_redex1_ineq : ineq -> (tyvar * ty) option = (*{{{*)
  fun (t1,t2) ->
    match t1, t2 with
    | TyVar a, TyVar b -> None
    | _, TyVar b -> Some (b, fleshize t1)

    | TyArrow(t11,t12) ,TyArrow(t21,t22) ->
        (match search_redex1_ineq (t11,t21) with
        | None -> search_redex1_ineq (t12, t22)
        | x    -> x)

    | TyInt, TyBool
    | TyInt, TyArrow _
    | TyBool, TyInt
    | TyBool, TyArrow _
    | TyArrow _, TyInt
    | TyArrow _, TyBool ->
        raise (Unification("inequation `" ^ show_ty t1 ^ " <= " ^ show_ty t2 ^ "` has no solution"))

    | _, TyInt
    | _, TyBool
    | _, TyArrow(_,_) -> None
(*}}}*)
let rec search_redex1 : asup -> (tyvar * ty) option = function(*{{{*)
  | [] -> None
  | (t1,t2)::l ->
      match search_redex1_ineq (t1, t2) with
      | None -> search_redex1 l
      | x    -> x
(*}}}*)

let search_nikai_shutsugen_var_path : ty -> (path * path) option =(*{{{*)
  fun ty ->
    let rec f : (tyvar * path) list -> path -> ty ->
               ((tyvar * path) list, (path * path)) either =
      fun l p t ->
        match t with
        | TyVar a ->
            (try Right(List.assoc a l, p)
            with Not_found -> Left((a,p)::l))
        | TyArrow(t1,t2) ->
            (match f l (L::p) t1 with
            | Left l' -> f l' (R::p) t2
            | right_x -> right_x)
        | TyInt
        | TyBool -> Left l in
    match f [] [] ty with
    | Right x -> Some x
    | _ -> None
(*}}}*)
let ty_of_path : ty -> path -> ty option =(*{{{*)
  fun t p ->
    let rec f p t =
      match p, t with
      | [], _ -> Some t
      | L::p', TyArrow(t1,t2) -> f p' t1
      | R::p', TyArrow(t1,t2) -> f p' t2
      | _ -> None in
    f (List.rev p) t
(*}}}*)
let rec not_occur : tyvar -> ty -> bool =(*{{{*)
  fun a -> function
    | TyVar b when a=b -> false
    | TyVar _          -> true
    | TyArrow (tau1, tau2) ->
        not_occur a tau1 && not_occur a tau2
    | TyInt
    | TyBool -> true
(*}}}*)
let rec search_redex2_ineq : ineq -> (tyvar * ty) option =(*{{{*)
  fun (t1,t2) ->
    match search_nikai_shutsugen_var_path t1 with
    | None -> None
    | Some (p1,p2) ->
        match ty_of_path t2 p1, ty_of_path t2 p2 with
        | Some s1, Some s2 ->
            let rec f : ty -> ty -> (tyvar * ty) option =
              fun t1 t2 ->
                (match t1,t2 with
                | TyVar a, TyVar b when a=b -> None
                | TyVar a, _ when not_occur a t2 -> Some (a, t2)
                | TyVar a, _ -> raise (Unification "Occur Check")

                | TyInt, TyVar b
                | TyBool, TyVar b -> Some (b, t1)

                | TyArrow(t11,t12), TyArrow(t21,t22) ->
                    (match f t11 t21 with
                    | None -> f t12 t22
                    | x    -> x)
                | _ -> None)in
            f s1 s2
        | _ -> raise (Unification "search_redex2_ineq: Type match error")
(*}}}*)
let rec search_redex2 : asup -> (tyvar * ty) option = function(*{{{*)
  | [] -> None
  | (t1,t2)::l ->
      match search_redex2_ineq (t1, t2) with
      | None -> search_redex2 l
      | x    -> x
(*}}}*)


let solve_asup : asup -> ty -> (ty * asup) =(*{{{*)
  fun asup ty ->
    let rec f : ty -> asup -> (ty * asup) =
      fun ty asup ->
        match search_redex1 asup with
        | None ->
            (match search_redex2 asup with
            | None -> (ty,asup)
            | Some hoge ->
                f (ty_subst [hoge] ty) (asup_subst [hoge] asup))
        | Some hoge ->
            f (ty_subst [hoge] ty) (asup_subst [hoge] asup) in
    f ty asup
(*}}}*)
let solve_asup : asup -> (subst * asup) =(*{{{*)
  fun asup ->
    let rec f : subst -> asup -> (subst * asup) =
      fun sbst asup ->
        match search_redex1 asup with
        | None ->
            (match search_redex2 asup with
            | None -> (sbst,asup)
            | Some hoge ->
                f (compose [hoge] sbst) (asup_subst [hoge] asup))
        | Some hoge ->
            f (compose [hoge] sbst) (asup_subst [hoge] asup) in
    f [] asup
(*}}}*)

(* main *)
let infer_expr : tyenv -> expr -> type_schema * tyenv =(*{{{*)
  fun tyenv e ->
    let e_star = label (rm_macro e) in
    let e_nf = theta_nf e_star in
    let (tau, asup) = asup_of_theta_nf tyenv e_nf in
    let sbst = fst (solve_asup asup) in
    let tau1 = ty_subst sbst tau in
    let sigma =
      let f s _ =
        let tv = new_var() in
        TsArrow(TsForall([tv], TsLift(TyVar tv)), s) in (* (∀ a.a)->s *)
      generalize_tyschme tyenv (List.fold_left f (TsLift tau1) e_nf.xs) in
    (sigma, tyenv)
    (*sigma, tyenv_subst sbst tyenv*)
(*}}}*)

(*test*)
let s = "let f x y = y in let a = f 1 in let b = f true in a=b;;"
let s = "(fun f -> f 1 = f true);;"
let s = "(fun x -> 3)(fun f -> f 1 + f 1);;"
let s = "(fun f -> if f 0 = f true then f 1 else f 3);;"
let e = match MyParser.toplevel MyLexer.main (Lexing.from_string s) with
    CExp e -> e | _ -> assert false

let e_star = label e
let e_nf = theta_nf e_star
let (tau, asup) = asup_of_theta_nf [] e_nf

let (sbst, asup') =  solve_asup asup
let tau' = ty_subst sbst tau
let clean_asup : asup -> asup =
  fun asup ->
    let f (t1,t2) =
      match t1, t2 with
      | TyArrow(TyVar a, TyVar b)
       ,TyArrow(t21,t22) when a=b && t21=t22 -> false
      | _ -> true in
    List.filter f asup
let asup'' = clean_asup asup'

(*TODO
 * labelの同名変数への対応(重要)
 * let rec(できれば)
 *)

