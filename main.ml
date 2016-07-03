open Syntax
open Eval
open Typecheck

let nub_by eq =
  let rec f = function
    | [] -> []
    | x::xs -> x :: f (List.filter (fun y -> not (eq x y)) xs)
  in f

let rec read_eval_print in_channel env tyenv =
  print_string "# ";
  flush stdout;
  try
    let cmd = MyParser.toplevel MyLexer.main (Lexing.from_channel in_channel) in
    let (xtyvs, env', tyenv') = eval_command env tyenv cmd in
    let rm_dup l =
      List.rev (nub_by (fun (x,_,_) (y,_,_) -> x=y) (List.rev l)) in
    let print l =
      let f (x, tyschm, v) =
        (match x with
        | "-" -> Printf.printf "- : %s = " (show_tyschm tyschm)
        | _   -> Printf.printf "val %s : %s = " x (show_tyschm tyschm));
        print_value v;
        print_newline () in
      ignore (List.map f l) in
    print (rm_dup xtyvs);
    read_eval_print stdin env' tyenv'
  with
    | Exit
    | Failure("lexing: empty token") -> () (*<C-d>で終了*)

    | Use s ->
        let in_channel =
          try open_in s
          with Sys_error e -> print_endline e;stdin
        in read_eval_print in_channel env tyenv

    | Failure s -> print_endline s; read_eval_print stdin env tyenv
    | e -> print_endline (Printexc.to_string e); read_eval_print stdin env tyenv

let _ = read_eval_print stdin empty_env empty_tyenv
