open Syntax
open Eval
open Typecheck

let rec read_eval_print env tyenv =
  print_string "# ";
  flush stdout;
  try
    let cmd = MyParser.toplevel MyLexer.main (Lexing.from_channel stdin) in
    let (id, tyschm, new_env, new_tyenv, v) = eval_command env tyenv cmd in
    Printf.printf "%s : " id;
    print_tyschm tyschm;
    print_string " = ";
    print_value v;
    print_newline ();
    read_eval_print new_env new_tyenv
  with
    | Failure("lexing: empty token") -> () (*<C-d>で終了*)
    | e -> print_endline (Printexc.to_string e); read_eval_print env tyenv

let _ = read_eval_print empty_env empty_tyenv
