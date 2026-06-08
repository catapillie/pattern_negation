type sigdef = Sig of string list

type pat =
  | Pomega
  | Pconstr of string * pat list
  | Por of pat * pat
  | Pand of pat * pat
  | Pnot of pat

let rec display_pat = function
  | Pomega -> "_"
  | Pconstr (c, ps) when List.length ps = 0 -> c
  | Pconstr (c, ps) ->
      c ^ "(" ^ (List.map display_pat ps |> String.concat ", ") ^ ")"
  | Por (p1, p2) -> display_pat p1 ^ "|" ^ display_pat p2
  | Pand (p1, p2) -> display_pat p1 ^ "&" ^ display_pat p2
  | Pnot p -> "~(" ^ display_pat p ^ ")"

type var = Var of int list (* each element is a field access *)

type lambda =
  | Lsuccess of int
  | Lfailure
  | Lswitch of var * (string * lambda) list * lambda
  | Lcatch of lambda * int * lambda
  | Lraise of int

let display_var (Var l) =
  "." ^ (List.rev l |> List.map string_of_int |> String.concat ".")

let display_lambda =
  let is_oneliner = function
    | Lsuccess _ | Lfailure | Lraise _ -> true
    | _ -> false
  in
  let indent i = String.make (i * 4) ' ' in
  let rec display i = function
    | Lsuccess v -> indent i ^ Printf.sprintf "success %d" v
    | Lfailure -> indent i ^ "failure"
    | Lswitch (var, cases, default) ->
        indent i
        ^ Printf.sprintf "switch %s\n" (display_var var)
        ^ (List.map
             (fun (c, l) ->
               if is_oneliner l then
                 indent i ^ Printf.sprintf "| case %s -> %s" c (display 0 l)
               else
                 indent i
                 ^ Printf.sprintf "| case %s -> \n" c
                 ^ display (i + 1) l)
             cases
          |> String.concat "\n")
        ^ "\n" ^ indent i
        ^
        if is_oneliner default then "| default -> " ^ display 0 default
        else "| default -> \n" ^ display (i + 1) default
    | Lcatch (l1, code, l2) ->
        indent i ^ "catch\n"
        ^ display (i + 1) l1
        ^ "\n" ^ indent i
        ^ Printf.sprintf "with %d\n" code
        ^ display (i + 1) l2
    | Lraise v -> indent i ^ Printf.sprintf "raise %d" v
  in
  display 0
