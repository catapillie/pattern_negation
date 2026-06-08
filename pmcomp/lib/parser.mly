%{

open Ast 

%}

%token LPAREN RPAREN
%token PIPE AMPER
%token TILDA COMMA
%token UNDERSCORES
%token KW_SWITCH KW_CASE KW_SIG
%token <string> IDENT
%token STOP

%left PIPE
%left AMPER
%nonassoc TILDA
%nonassoc IDENT

%start <sigdef list * pat list> program

%%

program: ss=list(sigdef) KW_SWITCH ps=list(pm_case) STOP { ss, ps }

sigdef: KW_SIG cs=separated_nonempty_list(COMMA, IDENT) STOP { Sig cs }

pm_case: KW_CASE p=pattern { p }

pattern:
  | UNDERSCORES                                     { Pomega }
  | c=IDENT                                         { Pconstr (c, []) }
  | c=IDENT p=pattern                               { Pconstr (c, [p]) }
  | TILDA p=pattern                                 { Pnot p }
  | p1=pattern AMPER p2=pattern                     { Pand (p1, p2) }
  | p1=pattern PIPE p2=pattern                      { Por (p1, p2) }
  | LPAREN ps=separated_list(COMMA, pattern) RPAREN
    { match ps with
      | [p] -> p
      | _   -> Pconstr ("tup" ^ string_of_int (List.length ps), ps) }