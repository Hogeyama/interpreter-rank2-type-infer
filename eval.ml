
open Syntax
open Typecheck

exception Unbound of string

let failwith = Pervasives.failwith

type name = string
type env = (name * value) list
and  value  =
  | VInt    of int
  | VBool   of bool
  | VFun    of name * expr * env
  | VRecFun of name * name * expr * env

let empty_env = []
let extend x v env = (x, v) :: env

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
     | VFun _, VFun _
     | VRecFun _, VFun _
     | VFun _, VRecFun _
     | VRecFun _, VRecFun _ -> raise (Invalid_argument "(=): functional value")
     | _ -> raise (TypeMatchErr "(=)"))
  | ELt (e1,e2) ->
    let v1 = eval_expr env e1 in
    let v2 = eval_expr env e2 in
    (match v1, v2 with
     | VInt i1,  VInt i2  -> VBool (i1 < i2)
     | VBool b1, VBool b2 -> VBool (b1 < b2)
     | VFun _, VFun _
     | VRecFun _, VFun _
     | VFun _, VRecFun _
     | VRecFun _, VRecFun _ -> raise (Invalid_argument "(<): functional value")
     | _ -> raise (TypeMatchErr "(<)"))
  | EIf (e1,e2,e3) ->
    let v1 = eval_expr env e1 in
    (match v1 with
     | VBool b ->
       if b then eval_expr env e2 else eval_expr env e3
     | _ -> raise (TypeMatchErr "if"))
  | ELet (x,e1,e2)
  | EMacro (x,e1,e2) ->
    let v1 = eval_expr env e1
    in eval_expr (extend x v1 env) e2
  | EFun (x,e1)   -> VFun (x,e1,env)
  | ELetRec (f,x,e1,e2) ->
      let nenv = extend f (VRecFun (f,x,e1,env)) env
      in eval_expr nenv e2
  | EApp (e1,e2) ->
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      (match v1 with
        | VFun(x,e,oenv) ->
            eval_expr (extend x v2 oenv) e
        | VRecFun (f,x,e,oenv) ->
            let env' =
              extend x v2 (extend f v1 oenv)
            in eval_expr env' e
        | _ -> failwith "hoge")

exception Quit
let rec eval_command env tyenv c =
  match c with
  | CExp e ->
      (try
        let (tyschm, new_tyenv) = infer_cmd tyenv c in
        ("-", tyschm, env, new_tyenv, eval_expr env e)
      with TypeError s ->
        print_string "\n";
        let (tyschm, new_tyenv) = Rank2.infer_expr tyenv e in
        ("-", tyschm, env, new_tyenv, eval_expr env e))
  | CDecl (x,e) ->
      (try
        let (tyschm, new_tyenv) = infer_cmd tyenv (CExp e) in
        let v = eval_expr env e
        in ("val "^x, tyschm, extend x v env, (x,tyschm)::new_tyenv, v)
      with TypeError s ->
        print_string "\n";
        let (tyschm, new_tyenv) = Rank2.infer_expr tyenv e in
        let v = eval_expr env e in
        ("val "^x, tyschm, extend x v env, (x,tyschm)::new_tyenv, v))
  | CRecDecl (f,x,e) ->
      eval_command env tyenv (CDecl (f,ELetRec(f,x,e,EVar f)))

let print_value = function
  | VInt n    -> print_int n
  | VBool b   -> print_string (string_of_bool b)
  | VFun _    -> print_string "<fun>"
  | VRecFun _ -> print_string "<rec fun>"

