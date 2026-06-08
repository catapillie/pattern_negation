{ open Parser }

let ident = ['a'-'z' 'A'-'Z' '0'-'9' '\'']+
let wildcard = ['_']+

rule token = parse
  | [' ' '\t' '\n']     { token lexbuf }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '|'                 { PIPE }
  | '&'                 { AMPER }
  | '~'                 { TILDA }
  | ','                 { COMMA }
  | ";;"                { STOP }
  | "switch"            { KW_SWITCH }
  | "case"              { KW_CASE }
  | "sig"               { KW_SIG }
  | wildcard            { UNDERSCORES }
  | ident as i          { IDENT i }
  
