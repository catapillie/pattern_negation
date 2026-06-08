open Pmcomp

type 'a rule = (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a

let syntax_error_message (lexbuf : Lexing.lexbuf) : string =
  let start = Lexing.lexeme_start_p lexbuf in
  let start_col = start.pos_cnum - start.pos_bol in
  "in file \"" ^ start.pos_fname ^ "\" at line "
  ^ string_of_int start.pos_lnum
  ^ ", column " ^ string_of_int start_col ^ "."

let parse_with (rule : 'a rule) (chan : in_channel) (filename : string) :
    'a option =
  let lexbuf = Lexing.from_channel chan in
  Lexing.set_filename lexbuf filename;
  try Some (rule Lexer.token lexbuf)
  with Parser.Error ->
    print_endline ("Syntax error " ^ syntax_error_message lexbuf);
    None

let () =
  if Array.length Sys.argv < 2 then begin
    print_endline "USAGE: ./pmcomp <path>";
    exit 1
  end;
  let path = Sys.argv.(1) in
  let chan = open_in path in
  let ast = parse_with Parser.program chan path in
  close_in chan;
  match ast with
  | None -> ()
  | Some (sigs, ps) ->
      if Exhaust.is_partial ps sigs then
        print_endline "Pattern-matching is partial."
      else print_endline "Pattern-matching is exhaustive.";
      let pm = Compile.initial_pm ps in
      let var = Compile.initial_var in
      let _l = Compile.translate pm [ var ] Lfailure in
      print_endline "Done."
