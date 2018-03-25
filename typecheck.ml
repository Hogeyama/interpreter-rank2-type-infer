
open Syntax

let debug_mode = false

(*{{{type宣言他*)
exception Unify of string
exception TypeError of string

type tyvar = int
type ty = TyInt | TyBool | TyArrow of ty * ty | TyVar of tyvar
type type_schema =
  | TsLift   of ty
  | TsForall of tyvar list * type_schema
  | TsArrow  of type_schema * type_schema
let forall(l,tau) = TsForall(l, TsLift(tau))

type subst  = (tyvar * ty) list
type constr = (ty * ty) list
type tyenv  = (name * type_schema) list

let empty_tyenv = []
let var_cnt = ref 0
let new_var () = var_cnt := !var_cnt+1; !var_cnt

let sprintf = Printf.sprintf


let rec take n l =
  if n<1 then [] else
  match n,l with
    | _, [] -> []
    | 1, (x::_)  -> [x]
    | _, (x::xs) -> x :: take (n-1) xs

let nub l =
  let l' = List.sort compare l in
  let rec f = function
    | [] -> []
    | [x] -> [x]
    | x::y::rest when x=y -> f (y::rest)
    | x::y::rest          -> x::(f (y::rest))
  in f l'

(*}}}*)

(*show, print*)
let rec get_type_vars : ty -> tyvar list = (*{{{*)
  fun l ->
    let f =function
      | TyVar a -> [a]
      | TyArrow (tau1,tau2) -> get_type_vars tau1 @ get_type_vars tau2
      | _ -> []
    in nub (f l)
(*}}}*)
let rec get_type_vars_tyschm : type_schema -> tyvar list = (*{{{*)
  function
    | TsLift tau -> get_type_vars tau
    | TsForall(_,sigma) -> get_type_vars_tyschm sigma
    | TsArrow(sigma1, sigma2) -> nub (get_type_vars_tyschm sigma1 @ get_type_vars_tyschm sigma2)
(*}}}*)
(*{{{*)
(*debug mode*)
let show_tyvar : tyvar -> string =(*{{{*)
  fun n -> sprintf "a%d" n
(*}}}*)
let rec show_ty_debug : ty -> string =(*{{{*)
  function
    | TyVar tv ->
        show_tyvar tv
    | TyArrow (tau1,tau2) ->
        let s1 = show_ty_debug tau1 in
        let s2 = show_ty_debug tau2 in
        let s1'=
          if String.contains s1 '>'
            then "("^s1^")" else s1 in
        s1' ^ " -> " ^ s2

    | TyInt -> "int"
    | TyBool -> "bool"

(*}}}*)
let print_ty_debug : ty -> unit = (*{{{*)
  fun tau -> print_string (show_ty_debug tau)
(*}}}*)
let rec show_tyschm_debug : type_schema -> string =(*{{{*)
  function
    | (TsLift tau) ->
        show_ty_debug tau
    | (TsForall(l,sigma)) ->
        let rec f = function
          | [] -> ""
          | [tv] -> show_tyvar tv
          | tv::l -> show_tyvar tv ^ " " ^ f l
        in sprintf "forall %s. %s" (f l) (show_tyschm_debug sigma)
    | TsArrow(sigma1, sigma2) ->
        let s1 = "(" ^ show_tyschm_debug sigma1 ^ ")" in
        let s2 = "(" ^ show_tyschm_debug sigma2 ^ ")" in
        s1 ^ " -> " ^ s2

(*}}}*)
let print_tyschm_debug : type_schema -> unit =(*{{{*)
  fun tyschm -> print_string (show_tyschm_debug tyschm)
(*}}}*)
(*normal*)
let rec get_map_ty : ty -> (tyvar * string) list =(*{{{*)
  fun tau ->
    let tvs = get_type_vars tau in
    if List.length tvs <= 27
      then
        let abc = ["a";"b";"c";"d";"e";"f";"g";"h";"i"
                  ;"j";"k";"l";"m";"n";"o";"p";"q";"r"
                  ;"s";"t";"u";"v";"w";"x";"y";"z"] in
        List.combine tvs (take (List.length tvs) abc)
      else
        let rec f n =
          if n=0 then [] else ("a"^string_of_int n)::f(n-1) in
        List.combine
            (List.sort compare tvs)
            (List.rev (f (List.length tvs)))
let rec get_map_tyschm : type_schema -> (tyvar * string) list =
  fun sigma ->
    let tvs = get_type_vars_tyschm sigma in
    if List.length tvs <= 27
      then
        let abc = ["a";"b";"c";"d";"e";"f";"g";"h";"i"
                  ;"j";"k";"l";"m";"n";"o";"p";"q";"r"
                  ;"s";"t";"u";"v";"w";"x";"y";"z"] in
        List.combine tvs (take (List.length tvs) abc)
      else
        let rec f n =
          if n=0 then [] else ("a"^string_of_int n)::f(n-1) in
        List.combine
            (List.sort compare tvs)
            (List.rev (f (List.length tvs)))


(*}}}*)
let show_ty_normal : ty -> string = (*{{{*)
  fun tau ->
    let map = get_map_ty tau in
    let rec f = function
      | TyInt -> "int"
      | TyBool -> "bool"
      | TyVar tv ->
          List.assoc tv map
      | TyArrow (tau1,tau2) ->
          let s1 =
            (match tau1 with
            | TyVar _
            | TyInt
            | TyBool -> f tau1

            | TyArrow _ ->"("^f tau1^")") in

          let s2 = f tau2 in
          (s1 ^ " -> " ^ s2)
    in f tau
(*}}}*)
let print_ty_normal : ty -> unit =(*{{{*)
  fun tau -> print_string (show_ty_normal tau)
(*}}}*)
let rec show_tyschm_normal : type_schema -> string =(*{{{*)
  fun sigma ->
    let map = get_map_tyschm sigma in
    let rec g map = function
      | TsLift tau ->
          show_ty_normal tau
      | TsForall(l,sigma) ->
          (match l with
            | [] ->
                g map sigma
            | _ ->
                let rec f = function
                  | [] -> ""
                  | [tv]  -> List.assoc tv map
                  | tv::l -> List.assoc tv map ^ " " ^ f l
                in sprintf "forall %s. %s" (f l) (g map sigma))
      | TsArrow(sigma1,sigma2) ->
          let s1 = "(" ^ g map sigma1 ^ ")" in
          let s2 = g map sigma2 in
          s1 ^ " -> " ^ s2 in
    g map sigma
(*}}}*)
let print_tyschm_normal : type_schema -> unit =(*{{{*)
  fun tyschm -> print_string (show_tyschm_normal tyschm)
(*}}}*)
(*}}}*)
let show_ty      : ty          -> string =(*{{{*)
  if debug_mode then show_ty_debug else show_ty_normal
(*}}}*)
let show_tyschm  : type_schema -> string =(*{{{*)
  if debug_mode then show_tyschm_debug else show_tyschm_normal
(*}}}*)
let print_ty     : ty          -> unit   =(*{{{*)
  if debug_mode then print_ty_debug else print_ty_normal
(*}}}*)
let print_tyschm : type_schema -> unit   =(*{{{*)
  if debug_mode then print_tyschm_debug else print_tyschm_normal
(*}}}*)
let show_constr  : constr -> string = (*{{{*)
  fun c ->
    let rec f = function
      | [] -> ""
      | [(t1,t2)]  -> show_ty_debug t1 ^ "=" ^ show_ty_debug t2
      | (t1,t2)::c -> show_ty_debug t1 ^ "=" ^ show_ty_debug t2 ^ ", " ^ f c
    in f c(*}}}*)
let show_subst   : subst  -> string = (*{{{*)
  fun sbst ->
    let rec f = function
      | [] -> ""
      | [(tv,t)]      -> show_tyvar tv ^ "=" ^ show_ty_debug t
      |  (tv,t)::sbst -> show_tyvar tv ^ "=" ^ show_ty_debug t ^ ", " ^ f sbst
    in f sbst
(*}}}*)
let print_subst  : subst  -> unit = (*{{{*)
  fun sbst -> print_string (show_subst sbst)
(*}}}*)

(*subst*)
let rec ty_subst : subst -> ty -> ty = (*{{{*)
  fun sbst tau ->
    match tau with
    | TyVar a ->
        (try  List.assoc a sbst
         with Not_found -> tau)
    | TyArrow (tau1, tau2) ->
        TyArrow ((ty_subst sbst tau1), (ty_subst sbst tau2))
    | _ -> tau
(*}}}*)
let rec tyschm_subst : subst -> type_schema -> type_schema = (*{{{*)
  fun sbst sigma ->
    match sigma with
    | TsLift tau ->
        TsLift (ty_subst sbst tau)
    | TsForall(l, sigma) ->
        let sbst' = List.filter (fun (a,_) -> not (List.mem a l)) sbst in
        TsForall(l, tyschm_subst sbst' sigma)
    | TsArrow (sigma1, sigma2) ->
        TsArrow (tyschm_subst sbst sigma1, tyschm_subst sbst sigma2)
(*}}}*)
let rec compose : subst -> subst -> subst =(*{{{*)
  fun sbst1 sbst2 ->
    let sbst1' =
      List.filter (fun (a,_) -> not (List.mem_assoc a sbst2)) sbst1 in
      (* sbst1のうちsbst2の定義域にないもの *)
    let sbst2' =
      let f (a, tau) = (a, ty_subst sbst1 tau) in
      List.map f sbst2 in
    sbst1'@sbst2'
(*}}}*)
let constr_subst : subst -> constr -> constr = (*{{{*)
  fun sbst constr ->
    let f (t1,t2) = (ty_subst sbst t1, ty_subst sbst t2) in
    List.map f constr
(*}}}*)
let tyenv_subst : subst -> tyenv -> tyenv = (*{{{*)
  fun sbst tyenv ->
    let f (x, sigma) = (x, tyschm_subst sbst sigma) in
    List.map f tyenv
(*}}}*)

(*unify*)
let rec not_occur : tyvar -> ty -> bool =(*{{{*)
  fun a -> function
    | TyVar b when a=b -> false
    | TyArrow (tau1, tau2) ->
        not_occur a tau1 && not_occur a tau2
    | _ -> true
(*}}}*)
let rec ty_unify : constr -> subst = function(*{{{*)
  | [] -> []
  | (s,t)::rest when s=t -> ty_unify rest

  | (TyArrow (s1,s2), TyArrow (t1,t2))::rest ->
      ty_unify ((s1,t1)::(s2,t2)::rest)

  | (TyVar a, t)::rest
  | (t, TyVar a)::rest when not_occur a t = true ->
      compose (ty_unify (constr_subst [(a,t)] rest)) [(a,t)]

  | (TyVar a, t)::rest
  | (t, TyVar a)::rest ->
      raise(TypeError "Unify: Occur Check")

  | (t1,t2)::_ -> raise(TypeError ("Unify: " ^ show_ty t1 ^ " is not compatible with " ^ show_ty t2))
(*}}}*)

(*type_schema関係*)
let instantiate : type_schema -> ty = (*{{{*)
  function
    | TsForall(l, TsLift tau) ->
        let f tv =
          let tv' = new_var()
          in (tv, TyVar tv') in
        let sbst = List.map f l in
        ty_subst sbst tau
    | _ -> assert false
let rec instantiate : type_schema -> ty = 
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
          raise(TypeError "rank 3 required")
      | TsForall(l, sigma1) ->
          let tau = instantiate sigma1 in
          let f tv =
            let tv' = new_var()
            in (tv, TyVar tv') in
          let sbst = List.map f l in
          ty_subst sbst tau
      | TsArrow(sigma1, sigma2) when is_quaunified sigma ->
          raise(TypeError "rank 3 required")
      | TsArrow(sigma1, sigma2) ->
          let tau1 = instantiate sigma1 in
          let tau2 = instantiate sigma2 in
          TyArrow(tau1,tau2)
(*}}}*)
let rec ftvs_of_tyschm : type_schema -> tyvar list = (*{{{*)
  function
    | TsForall(l, sigma) ->
        List.filter (fun tv -> not (List.mem tv l)) (ftvs_of_tyschm sigma)
    | TsLift tau ->
        get_type_vars tau
    | TsArrow(sigma1, sigma2) ->
        nub (ftvs_of_tyschm sigma1 @ ftvs_of_tyschm sigma2)
    (*| s -> print_tyschm s; print_string " "; assert false*)
(*}}}*)
let ftvs_of_tyenv : tyenv -> tyvar list = (*{{{*)
  fun tyenv ->
    let f (_,schm) = ftvs_of_tyschm schm in
    List.concat (List.map f tyenv)
(*}}}*)
let generalize : tyenv -> ty -> type_schema = (*{{{*)
  fun tyenv tau ->
    let ftvs_tyenv = ftvs_of_tyenv tyenv in
    let ftvs =
      nub (List.filter (fun tv -> not (List.mem tv ftvs_tyenv)) (get_type_vars tau)) in
    TsForall(ftvs, TsLift tau)
(*}}}*)
let generalize_tyschme : tyenv -> type_schema -> type_schema = (*{{{*)
  fun tyenv sigma ->
    let ftvs_tyenv = ftvs_of_tyenv tyenv in
    let ftvs =
      nub (List.filter (fun tv -> not (List.mem tv ftvs_tyenv)) (ftvs_of_tyschm sigma)) in
    TsForall(ftvs, sigma)
(*}}}*)

(*infer*)
let rec infer_expr : tyenv -> expr -> ty * constr = (*{{{*)
  fun tyenv e -> match e with
    | EConstInt _ -> (TyInt, [])
    | EConstBool _ -> (TyBool, [])
    | EVar x ->
        (try (instantiate (List.assoc x tyenv), [])
         with Not_found -> raise(TypeError ("infer_expr: '" ^ x ^ "' Not_found")))
    | EAdd (e1,e2)
    | ESub (e1,e2)
    | EMul (e1,e2)
    | EDiv (e1,e2) ->
        let (t1,c1) = infer_expr tyenv e1 in
        let (t2,c2) = infer_expr tyenv e2 in
        (TyInt, (t1,TyInt)::(t2,TyInt)::c1@c2)
    | EEq (e1,e2)
    | ELt (e1,e2) ->
        let (t1,c1) = infer_expr tyenv e1 in
        let (t2,c2) = infer_expr tyenv e2 in
        (TyBool, (t1,t2)::c1@c2)
    | EIf (e1,e2,e3) ->
        let (t1,c1) = infer_expr tyenv e1 in
        let (t2,c2) = infer_expr tyenv e2 in
        let (t3,c3) = infer_expr tyenv e3 in
        (t2, (t1,TyBool)::(t2,t3)::c1@c2@c3)
    | EFun (x,e1) ->
        let tv = new_var() in
        let tmp_tyenv = (x,TsForall([],TsLift (TyVar tv)))::tyenv in
        let (t,c) = infer_expr tmp_tyenv e1 in
        (TyArrow(TyVar tv, t), c)
    | EApp (e1,e2) ->
        let tv = new_var() in
        let (t1,c1) = infer_expr tyenv e1 in
        let (t2,c2) = infer_expr tyenv e2 in
        (TyVar tv, (t1,TyArrow(t2,TyVar tv))::c1@c2)
    | ELet (x,e1,e2)
    | EMacro (x,e1,e2) ->
        let (t1,c1) = infer_expr tyenv e1 in
        let sbst = ty_unify c1 in
        let s1 = ty_subst sbst t1 in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschm = generalize new_tyenv s1 in
        let (t,c) = infer_expr ((x,tyschm)::tyenv) e2 in
        (t, c@c1)
    | ELetRec (f,x,e1,e2) -> (*###*)
        let tv1 = new_var() in
        let tv2 = new_var() in
        let tmp_tyenv =
          (x,forall([],TyVar tv1))
          ::(f,forall([],TyArrow(TyVar tv1, TyVar tv2)))::[] in
        let (t1,c1) = infer_expr tmp_tyenv e1 in
        let sbst = ty_unify c1 in
        let s1 = TyArrow(ty_subst sbst (TyVar tv1), ty_subst sbst t1) in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschm = generalize new_tyenv s1 in
        let (t,c) = infer_expr ((f,tyschm)::tyenv) e2 in
        (t, c@c1)




(*}}}*)
let infer_cmd : tyenv -> command -> type_schema * tyenv =(*{{{*)
  fun tyenv cmd -> match cmd with
    | CExp e ->
        let (t,c) = infer_expr tyenv e in
        let sbst = ty_unify c in
        let s = ty_subst sbst t in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschm = generalize new_tyenv s in
        (tyschm, new_tyenv)
    | CDecl (x,e) ->
        let (t,c) = infer_expr tyenv e in
        let sbst = ty_unify c in
        let s = ty_subst sbst t in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschm = generalize new_tyenv s in
        (tyschm, (x,tyschm)::new_tyenv)
    | _ -> failwith "infer_cmd: Not Implemented"
(*}}}*)

