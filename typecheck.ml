open Syntax

let debug_mode = true

(*{{{type宣言他*)
exception Unification of string

type subst  = (tyvar * ty) list
type constr = (ty * ty) list
type tyenv  = (name * type_schema) list

let empty_tyenv = []
let var_cnt = ref 0
let new_var () =
  var_cnt := !var_cnt+1; (TV (Left !var_cnt))
let new_var_with_name s = TV (Right s)

(*便利な関数{{{*)
let sprintf = Printf.sprintf

let rec take n l =
  if n<1 then [] else
  match n,l with
    | _, [] -> []
    | 1, (x::_)  -> [x]
    | _, (x::xs) -> x :: take (n-1) xs

let rec nub = function
  | [] -> []
  | x::xs -> x :: nub (List.filter (fun y -> x <> y) xs)

let is_substring s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

let rec lefts : ('a, 'b) either list -> 'a list =
  function
  | [] -> []
  | (Right _)::xs -> lefts xs
  | (Left  x)::xs -> x :: lefts xs

let rec rights : ('a, 'b) either list -> 'b list =
  function
  | [] -> []
  | (Left   _)::xs -> rights xs
  | (Right  x)::xs -> x :: rights xs

let rec cat_options : 'a option list -> 'a list =
  function
  | [] -> []
  | None::xs -> cat_options xs
  | (Some x)::xs -> x :: cat_options xs

let diff : 'a list -> 'a list -> 'a list =
  fun xs ys ->
    let rec delete ys x = match ys with
      | []  -> []
      | y::ys when x = y -> ys
      | y::ys            -> y :: delete ys x in
    List.fold_left delete xs ys
(*}}}*)

(*}}}*)

(*show, print*)
let rec get_type_vars : ty -> tyvar list = (*{{{*)
  fun l ->
    let f =function
      | TyVar a -> [a]
      | TyArrow (tau1,tau2)
      | TyPair  (tau1,tau2) ->
          let tvs1 = get_type_vars tau1 in
          let tvs2 = get_type_vars tau2 in
          tvs1@tvs2
      | TyList tau1 -> get_type_vars tau1
      | TyInt
      | TyBool -> [] in
    nub (f l)
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
  function
  | TV (Left n) -> sprintf "'a%d" n
  | TV (Right s) -> "'" ^ s
(*}}}*)
let rec show_ty_debug : ty -> string =(*{{{*)
  function
    | TyVar tv ->
        show_tyvar tv
    | TyArrow (tau1,tau2) ->
        let s1 = show_ty_debug tau1 in
        let s2 = show_ty_debug tau2 in
        "(" ^ s1 ^ ")" ^ " -> " ^ s2

    | TyInt -> "int"
    | TyBool -> "bool"

    | TyPair (tau1, tau2) ->
        let s1 = show_ty_debug tau1 in
        let s2 = show_ty_debug tau2 in
        "(" ^ s1 ^ "," ^ s2 ^ ")"

    | TyList tau ->
        "(" ^ show_ty_debug tau ^ ")" ^ " list"
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
let rec get_map : ty -> (tyvar * string) list = (*{{{*)
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
(*}}}*)
let rec get_map_tyschm : type_schema -> (tyvar * string) list = (*{{{*)
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
    let map = get_map tau in
    let rec f = function
      | TyInt -> "int"
      | TyBool -> "bool"
      | TyVar (TV(Left _) as tv) ->
          "'" ^ List.assoc tv map
      | TyVar TV(Right s) ->
          "'" ^ s
      | TyArrow (tau1,tau2) ->
          let s1 =
            (match tau1 with
            | TyVar _
            | TyList _
            | TyInt
            | TyBool -> f tau1

            | TyPair _
            | TyArrow _ ->"("^f tau1^")") in

          let s2 = f tau2 in
          (s1 ^ " -> " ^ s2)

      | TyPair (tau1, tau2) ->
          let s1 =
            (match tau1 with
            | TyVar _
            | TyList _
            | TyInt
            | TyBool -> f tau1

            | TyPair _
            | TyArrow _ -> "("^f tau1^")") in

          let s2 =
            (match tau2 with
            | TyVar _
            | TyList _
            | TyInt
            | TyBool -> f tau2

            | TyPair _
            | TyArrow _ -> "("^f tau2^")") in
          s1 ^ " * " ^ s2

      | TyList tau1 ->
          (match tau1 with
          | TyVar _
          | TyList _
          | TyInt
          | TyBool -> f tau1 ^ " list"

          | TyPair _
          | TyArrow _ -> "("^f tau1^")"^ " list")
    in f tau
    (* TODO DRY *)
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
    | TyPair (tau1, tau2) ->
        TyPair ((ty_subst sbst tau1), (ty_subst sbst tau2))
    | TyList tau1 ->
        TyList (ty_subst sbst tau1)
    | TyInt
    | TyBool -> tau
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

(*unify*)
let rec not_occur : tyvar -> ty -> bool =(*{{{*)
  fun a -> function
    | TyVar b when a=b -> false
    | TyVar _          -> true
    | TyArrow (tau1, tau2)
    | TyPair  (tau1, tau2) ->
        not_occur a tau1 && not_occur a tau2
    | TyList tau1 ->
        not_occur a tau1
    | TyInt
    | TyBool -> true

    (*| _ -> true*)
(*}}}*)
let rec ty_unify : constr -> subst = function(*{{{*)
  | [] -> []
  | (s,t)::rest when s=t -> ty_unify rest

  | (TyArrow (s1,s2), TyArrow (t1,t2))::rest
  | (TyPair  (s1,s2), TyPair  (t1,t2))::rest ->
      ty_unify ((s1,t1)::(s2,t2)::rest)

  | (TyList s, TyList t)::rest ->
      ty_unify ((s,t)::rest)

  (* 一番上がないと let f : 'b -> 'b = fun x -> x
   * の型が 'a -> 'a と表示されてしまうかも *)
  | (TyVar(TV(Right _)) as t, TyVar(TV(Left _) as a))::rest
  | (TyVar a, t)::rest
  | (t, TyVar a)::rest when not_occur a t = true ->
      compose (ty_unify (constr_subst [(a,t)] rest)) [(a,t)]

  | (TyVar a, t)::rest
  | (t, TyVar a)::rest ->
      raise (Unification "Occur Check")

  | (TyArrow _, TyInt)::_
  | (TyInt, TyArrow _)::_ ->
      raise (Unification "Int is not compatible with arrow type ")

  | (TyArrow _, TyBool)::_
  | (TyBool, TyArrow _)::_ ->
      raise (Unification "Bool is not compatible with arrow type ")

  | _ -> raise (Unification "uwaa") (* ###注意### *)
(*}}}*)

(*type_schema関係*)
let rec instantiate : type_schema -> ty = (*{{{*)
  fun sigma ->
    match sigma with
      | TsLift tau -> tau
      | TsForall(l, sigma1) ->
          let tau = instantiate sigma1 in
          let f tv =
            let tv' = new_var()
            in (tv, TyVar tv') in
          let sbst = List.map f l in
          ty_subst sbst tau
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

(*infer*)
let rec infer_pattern : pattern -> ty * tyenv * constr =(*{{{*)
(* 例 (x, y::l) => (tx*tl), [(x:tx),(y:ty),(l:tl)], [tl = ty list] *)
  fun p ->
    match p with
    | PInt  _ -> (TyInt , [], [])
    | PBool _ -> (TyBool, [], [])
    | PVar  x ->
        let tvx = new_var () in
        (TyVar tvx, [(x, TsLift(TyVar tvx))], [])
    | PPair (p1,p2) ->
        let (tp1, tyenv1, c1) = infer_pattern p1 in
        let (tp2, tyenv2, c2) = infer_pattern p2 in
        (TyPair(tp1, tp2), tyenv1@tyenv2, c1@c2)
    | PNil ->
        let tv = new_var () in
        (TyList (TyVar tv), [], [])
    | PCons (p1, p2) ->
        let (tp1, tyenv1, c1) = infer_pattern p1 in
        let (tp2, tyenv2, c2) = infer_pattern p2 in
        (tp2, tyenv1@tyenv2, (tp2, TyList(tp1))::c1@c2)

    (* TODO p中に同じ変数が複数回でたらエラーを出すべき. *)
(*}}}*)
let rec constr_type_expr : tyenv -> expr -> ty * constr = (*{{{*)
  fun tyenv e -> match e with
    | EConstInt _ -> (TyInt, [])
    | EConstBool _ -> (TyBool, [])
    | EVar x ->
        (try
          let tyschm = List.assoc x tyenv in
          (instantiate tyschm, [])
         with Not_found -> failwith ("constr_type_expr: '" ^ x ^ "' Not_found"))
    | EAdd (e1,e2)
    | ESub (e1,e2)
    | EMul (e1,e2)
    | EDiv (e1,e2) ->
        let (t1,c1) = constr_type_expr tyenv e1 in
        let (t2,c2) = constr_type_expr tyenv e2 in
        (TyInt, (t1,TyInt)::(t2,TyInt)::c1@c2)
    | EEq (e1,e2)
    | ELt (e1,e2) ->
        let (t1,c1) = constr_type_expr tyenv e1 in
        let (t2,c2) = constr_type_expr tyenv e2 in
        (TyBool, (t1,t2)::c1@c2)
    | EIf (e1,e2,e3) ->
        let (t1,c1) = constr_type_expr tyenv e1 in
        let (t2,c2) = constr_type_expr tyenv e2 in
        let (t3,c3) = constr_type_expr tyenv e3 in
        (t2, (t1,TyBool)::(t2,t3)::c1@c2@c3)
    | EFun (x,e1) ->
        let tv = new_var() in
        let tmp_tyenv = (x, TsLift(TyVar tv))::tyenv in
        let (t,c) = constr_type_expr tmp_tyenv e1 in
        (TyArrow(TyVar tv, t), c)
    | EApp (e1,e2) ->
        let tv = new_var() in
        let (t1,c1) = constr_type_expr tyenv e1 in
        let (t2,c2) = constr_type_expr tyenv e2 in
        (TyVar tv, (t1,TyArrow(t2,TyVar tv))::c1@c2)
    | ELet (l, e1) ->
        let (new_tyenv, c) = infer_decl tyenv (Decl l) in
        let (t, c') = constr_type_expr new_tyenv e1 in
        (t, c@c')
    | ELetTy ([x,tyschm,e1], e2) ->
        let ty = instantiate tyschm in
        let (ty', c) = constr_type_expr tyenv e1 in
        let sbst = ty_unify ((ty,ty')::c) in
        let new_ty = ty_subst sbst ty in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschm = generalize new_tyenv new_ty in
        let (t,c') = constr_type_expr ((x,tyschm)::new_tyenv) e2 in
        print_subst sbst;
        (t, c@c')

    | ELetTy _ -> assert false
    | ELetRec (l, e1) ->
        let (new_tyenv, c) = infer_decl tyenv (RecDecl l) in
        let (t, c') = constr_type_expr new_tyenv e1 in
        (t, c@c')
    | EPair (e1,e2) ->
        let (t1,c1) = constr_type_expr tyenv e1 in
        let (t2,c2) = constr_type_expr tyenv e2 in
        (TyPair(t1,t2), c1@c2)
    | ENil ->
        let tv = new_var() in
        (TyList (TyVar tv), [])
    | ECons (e1,e2) ->
        let (t1,c1) = constr_type_expr tyenv e1 in
        let (t2,c2) = constr_type_expr tyenv e2 in
        (t2, (TyList t1, t2)::c1@c2)
    | EMatch (e', l) ->
        let (te',c) = constr_type_expr tyenv e' in
        let te = TyVar (new_var ()) in (*全体の型*)
        let rec f (pi,ei) =
          let (tpi, tyenvpi, cpi) = infer_pattern pi in
          let (tei, ci) = constr_type_expr (tyenvpi@tyenv) ei in
          (te,tei)::(te',tpi)::ci@cpi in
        let cl = List.concat (List.map f l) in
        (te, cl)
(*}}}*)
and infer_decl : tyenv -> declare -> (tyenv * constr) = (*{{{*)
  fun tyenv dec ->
    match dec with
    | Decl l ->
        let (xs, es) = List.split l in
        let (ts,cs) = List.split (List.map (constr_type_expr tyenv) es) in
        let c = List.concat cs in
        let sbst = ty_unify c in
        let new_ts = List.map (ty_subst sbst) ts in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschms = List.map (generalize new_tyenv) new_ts in
        ((List.combine xs tyschms)@new_tyenv, c)
    | RecDecl l ->
        let fs = List.map (fun (f,x,e) -> f) l in
        let xs = List.map (fun (f,x,e) -> x) l in
        let es = List.map (fun (f,x,e) -> e) l in

        let tmp = List.map (fun _ -> (TyVar(new_var()),TyVar(new_var()))) fs in
        let (tyargs, tyrets) = List.split tmp in
        let tyfuns = List.map (fun (tyarg,tyret) -> TyArrow(tyarg,tyret)) tmp in

        let rec lift_combine xs tys = (* tyをtype_schemaに昇格しつつList.combine *)
          match xs,tys with
          | [],[] -> []
          | (x::xs),(ty::tys) -> (x, TsLift ty) :: lift_combine xs tys
          | _ -> failwith "Impossible" in

        let tmp_tyenv = (lift_combine xs tyargs)@(lift_combine fs tyfuns)@tyenv in
        let (tyrets', cs) = List.split (List.map (constr_type_expr tmp_tyenv) es) in
        let constr =
          (List.combine tyrets tyrets')@(List.concat cs) in
        let sbst = ty_unify constr in

        let new_tyfuns = List.map (ty_subst sbst) tyfuns in
        let new_tyenv  = tyenv_subst sbst tyenv in

        let tyschms = List.map (generalize new_tyenv) new_tyfuns in
        ((List.combine fs tyschms)@new_tyenv, constr)
(*}}}*)
let infer_cmd : tyenv -> command -> type_schema * tyenv = (*{{{*)
  fun tyenv cmd -> match cmd with
    | CExp e ->
        let (t,c) = constr_type_expr tyenv e in
        let sbst = ty_unify c in
        let s = ty_subst sbst t in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschm = generalize new_tyenv s in
        (tyschm, new_tyenv)
    (*
    | CDecl (x,e) ->
        let (t,c) = constr_type_expr tyenv e in
        let sbst = ty_unify c in
        let s = ty_subst sbst t in
        let new_tyenv = tyenv_subst sbst tyenv in
        let tyschm = generalize new_tyenv s in
        (tyschm, (x,tyschm)::new_tyenv)
    *)
    | _ -> failwith "infer_cmd: Not Implemented"
(*}}}*)
let infer_expr : tyenv -> expr -> type_schema * tyenv =(*{{{*)
  fun tyenv e ->
    let (t,c) = constr_type_expr tyenv e in
    let sbst = ty_unify c in
    let s = ty_subst sbst t in
    let new_tyenv = tyenv_subst sbst tyenv in
    let tyschm = generalize new_tyenv s in
    (tyschm, new_tyenv)
(*}}}*)

