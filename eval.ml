
open Syntax
open Typecheck

exception Unbound of string
exception Pattern_match of string

type name = string
type env = (name * value) list
and  value  =
  | VInt    of int
  | VBool   of bool
  | VFun    of name * expr * env
  | VRecFun of int * ((name * name * expr) list) * env
  | VPair   of value * value
  | VNil
  | VCons   of value * value

let rec find_match : pattern -> value -> (name * value) list option =
  fun p v -> match p, v with
  | PInt  n, VInt n' when n=n' -> Some []
  | PInt  n, VInt n'           -> None

  | PBool b, VBool b' when b=b' -> Some []
  | PBool b, VBool b'           -> None

  | PVar x, _ -> Some [(x,v)]

  | PPair (p1,p2), VPair(v1, v2) ->
      (match find_match p1 v1, find_match p2 v2 with
        | None, _
        | _, None -> None
        | Some l1, Some l2 -> Some (l1@l2))

  | PNil, VNil -> Some []

  | PCons (p1,p2), VCons (v1,v2) ->
      (match find_match p1 v1, find_match p2 v2 with
        | None, _
        | _, None -> None
        | Some l1, Some l2 -> Some (l1@l2))
  | _ -> None

let empty_env = []
let extend x v env = (x, v) :: env
let extend_list l env =
  let f env (x,v) = extend x v env in
  List.fold_left f env l

let rec lookup x env =
  try List.assoc x env with Not_found -> raise (Unbound x)

exception EvalErr
exception TypeMatchErr of string

let rec eval_expr env e =
  match e with
  | EConstInt i ->
    VInt i
  | EConstBool b ->
    VBool b
  | EVar x ->
       lookup x env
  | EAdd (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> VInt (i1 + i2)
     | _ -> raise (TypeMatchErr "(+)"))
  | ESub (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> VInt (i1 - i2)
     | _ -> raise (TypeMatchErr "(-)"))
  | EMul (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> VInt (i1 * i2)
     | _ -> raise (TypeMatchErr "(*)"))
  | EDiv (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1, VInt i2 -> VInt (i1 / i2)
     | _ -> raise (TypeMatchErr "(/)"))
  | EEq (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1,  VInt i2  -> VBool (i1 = i2)
     | VBool b1, VBool b2 -> VBool (b1 = b2)
     | _ -> raise (TypeMatchErr "(=)"))
  | ELt (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1,  VInt i2  -> VBool (i1 < i2)
     | VBool b1, VBool b2 -> VBool (b1 < b2)
     | _ -> raise (TypeMatchErr "(<)"))
  | EIf (e1,e2,e3) ->
    let v1 = eval_expr env e1 in
    (match v1 with
     | VBool b ->
       if b then eval_expr env e2 else eval_expr env e3
     | _ -> raise (TypeMatchErr "if"))
    (*
  | ELet (x,e1,e2) ->
    let v1 = eval_expr env e1
    in eval_expr (extend x v1 env) e2
     *)
  | ELet (l, e1) ->
      let f (x,e) = (x, eval_expr env e) in
      let tmp_env = extend_list (List.map f l) env in
      eval_expr tmp_env e1
  | EFun (x,e1)   -> VFun (x,e1,env)
  | ELetRec (l,e1) ->
      let rec func env' n = function
        | [] -> env'
        | (f,x,e)::rest ->
            let v = VRecFun (n, l, env)
            in func (extend f v env') (n+1) rest in
      let env' = func env 0 l in
      eval_expr env' e1
  | EApp (e1,e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match v1 with
        | VFun(x,e,oenv) ->
            eval_expr (extend x v2 oenv) e
        | VRecFun (i, l, oenv) ->
            let (_, xi, ei) = List.nth l i in
            let nenv =
              let rec func n env' = function
                | [] -> env'
                | (f,x,e)::rest ->
                    let nenv' = extend f (VRecFun(n,l,oenv)) env' in
                    func (n+1) nenv' rest in
              func 0 oenv l in
            eval_expr (extend xi v2 nenv) ei
        | _ -> raise EvalErr)
  | EPair (e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      VPair (v1, v2)
  | ENil -> VNil
  | ECons (e1, e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      VCons (v1, v2)
  | EMatch (e1, l) ->
      let v1 = eval_expr env e1 in
      let rec f = function
        | [] -> raise (Pattern_match "")
        | (p,e2)::l ->
            (match find_match p v1 with
              | None -> f l
              | Some xvs ->
                  let env' = extend_list xvs env in
                  eval_expr env' e2) in
      f l

(* dup 重複を検出 *)
let dup_by eq l =
  let rec f xs = function
    | [] -> None
    | y::ys when List.exists (eq y) xs -> Some y
    | y::ys -> f (y::xs) ys
  in f [] l

let eval_decl : env -> tyenv -> declare ->
                env * tyenv * (name * type_schema * value) list =
  fun env tyenv dec ->
    match dec with
    | Decl l ->
        (match dup_by (fun (x,_) (y,_) -> x=y) l with
        | Some (x,_) ->
            failwith ("Variable " ^ x ^ " is bound several times in this matching")
        | None ->
            let rec f = function
              | [] -> []
              | (x,e)::l' ->
                  let (tyschm, new_tyenv) = infer_expr tyenv e in
                  let v = eval_expr env e in
                  (x, tyschm, v) :: f l' in
            let xtyvs = f l in
            let g (x,tyschm,v) = (x,tyschm) in
            let h (x,tyschm,v) = (x,v) in
            let new_tyenv = (List.map g xtyvs) @ tyenv in
            let new_env   = (List.map h xtyvs) @ env in
            (new_env, new_tyenv, xtyvs))
    | RecDecl l ->
        (match dup_by (fun (x,_,_) (y,_,_) -> x=y) l with
        | Some (f,_,_) ->
            failwith ("Variable " ^ f ^ " is bound several times in this matching")
        | None ->
            let new_tyenv = infer_decl tyenv dec in
            let rec func n = function
              | [] -> []
              | (f,x,e)::l' ->
                  let tyschm = List.assoc f new_tyenv in
                  let v = VRecFun (n, l, env) in
                  (f, tyschm, v)::(func (n+1) l') in
            let xtyvs = func 0 l in
            let h (x,tyschm,v) = (x,v) in
            let new_env   = (List.map h xtyvs) @ env in
            (new_env, new_tyenv, xtyvs))

exception Use of string
let rec eval_command env tyenv c =
  match c with
  | CExp e ->
      let (tyschm, new_tyenv) = infer_cmd tyenv c in
      ([("-", tyschm, eval_expr env e)], env, new_tyenv)
  | CDecl declist ->
      let rec f xtyvs tyenv env = function
        | [] -> (xtyvs, env, tyenv)
        | dec::l ->
            let (env', tyenv', xtyvs') = eval_decl env tyenv dec in
            f (xtyvs@xtyvs') tyenv' env' l in
      f [] tyenv env declist
  | CDirect (s,args) ->
      (match s with
      | "quit" ->
          raise Exit
      | "use"  ->
          (match args with
          | [x] -> raise (Use x)
          | _   -> failwith "#use: wrong arguments number")
      | _ ->
          failwith ("eval_command: Unknown directive " ^ s))

let rec print_value = function
  | VInt n    -> print_int n
  | VBool b   -> print_string (string_of_bool b)
  | VFun _    -> print_string "<fun>"
  | VRecFun _ -> print_string "<rec fun>"
  | VPair (v1,v2) ->
      print_string "(";
      print_value v1;
      print_string ", ";
      print_value v2;
      print_string ")";
  | VNil -> print_string "[]"
  | VCons (v1,v2) ->
      let rec f v1 v2 =
        match v2 with
        | VNil ->
            print_value v1;
        | VCons (v21,v22) ->
            print_value v1;
            print_string "; ";
            f v21 v22
        | _ -> failwith "だめ" in
      print_string "[";
      f v1 v2;
      print_string "]";


