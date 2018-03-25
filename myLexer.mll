let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_' ] 
let ident = alpha (alpha | digit)* 

rule main = parse
| space+       { main lexbuf }
| "+"          { MyParser.PLUS }
| "*"          { MyParser.TIMES }
| "-"          { MyParser.MINUS }
| "/"          { MyParser.DIV }
| "="          { MyParser.EQ }
| "<"          { MyParser.LT }
| "let"        { MyParser.LET }
| "rec"        { MyParser.REC }
| "macro"      { MyParser.MACRO }
| "in"         { MyParser.IN }
| "if"         { MyParser.IF }
| "then"       { MyParser.THEN }
| "else"       { MyParser.ELSE }
| "true"       { MyParser.BOOL (true) }
| "false"      { MyParser.BOOL (false) }
| "("          { MyParser.LPAR }
| ")"          { MyParser.RPAR }
| "fun"        { MyParser.FUN}
| "->"         { MyParser.ARROW }
| ";;"         { MyParser.SEMISEMI }
| digit+ as n  { MyParser.INT (int_of_string n) }
| ident  as id { MyParser.ID id }
| _            { failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}
