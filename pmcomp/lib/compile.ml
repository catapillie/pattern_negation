open Ast

type pm = (pat list * lambda) list
type pm_nonempty = (pat * pat list * lambda) list
type var_row = var list
type var_row_nonempty = var * var list

let display_pm (mat : pm) =
  List.map
    (fun (row, i) ->
      Printf.sprintf "| %s" (List.map display_pat row |> String.concat "\t"))
    mat
  |> String.concat "\n"

let to_nonempty (mat : pm) : pm_nonempty =
  List.map (fun (l, v) -> (List.hd l, List.tl l, v)) mat

let to_nonempty_vars (vars : var_row) : var_row_nonempty =
  (List.hd vars, List.tl vars)

let var_case_accesses k (Var xs) : var list =
  List.init k (fun x -> Var (x :: xs))

let initial_pm (ps : pat list) : pm =
  List.mapi (fun i p -> ([ p ], Lsuccess i)) ps

let initial_var = Var []

(* trap-handler number allocation *)
let trap_code = ref 0

let alloc_trap_code () : int =
  incr trap_code;
  !trap_code

(* util *)
let rec takedrop_while_map p xs =
  match xs with
  | [] -> ([], [])
  | x :: xss -> (
      match p x with
      | Some y ->
          let h, t = takedrop_while_map p xss in
          (y :: h, t)
      | None -> ([], xs))

let try_take_map_head p = function
  | [] -> None
  | x :: xs -> ( match p x with None -> None | Some y -> Some (y, xs))

let rec translate (mat : pm) (vars : var_row) (failure : lambda) : lambda =
  (* print_endline (display_pm mat);
  print_endline ""; *)
  match mat with
  | [] -> failure
  | row1 :: _ -> (
      match row1 with
      | [], lam -> lam
      | _ ->
          translate_nonempty (to_nonempty mat) (to_nonempty_vars vars) failure)

and translate_nonempty (mat : pm_nonempty) ((var, vars) : var_row_nonempty)
    (failure : lambda) : lambda =
  let select_omegas (p, ps, i) =
    match p with Pomega -> Some (ps, i) | _ -> None
  in
  let select_constrs (p, ps, i) =
    match p with Pconstr (c, args) -> Some ((c, args), (ps, i)) | _ -> None
  in

  let select_not (p, ps, i) =
    match p with Pnot p -> Some (p, (ps, i)) | _ -> None
  in

  let select_or (p, ps, i) =
    let rec flatten_or = function
      | Por (p1, p2) -> flatten_or p1 @ flatten_or p2
      | p -> [ p ]
    in
    match p with Por (p1, p2) -> Some (flatten_or p, (ps, i)) | _ -> None
  in

  let pm_vars, mat = takedrop_while_map select_omegas mat in
  if pm_vars <> [] then translate_nonempty_vars pm_vars mat (var, vars) failure
  else
    let pm_constrs, mat = takedrop_while_map select_constrs mat in
    if pm_constrs <> [] then
      translate_nonempty_constrs pm_constrs mat (var, vars) failure
    else
      match try_take_map_head select_not mat with
      | Some (p, mat) -> translate_nonempty_not p mat (var, vars) failure
      | None -> (
          match try_take_map_head select_or mat with
          | Some ((qs, ps), mat) ->
              translate_nonempty_or qs ps mat (var, vars) failure
          | None -> failwith "Compile.translate_nonempty: stuck")

and translate_nonempty_vars (mat_vars : pm) (mat : pm_nonempty)
    ((var, vars) : var_row_nonempty) (failure : lambda) =
  let failure =
    if mat = [] then failure else translate_nonempty mat (var, vars) failure
  in
  translate mat_vars vars failure

and translate_nonempty_constrs pm_constrs (mat : pm_nonempty) (var, vars)
    failure =
  let failure =
    if mat = [] then failure else translate_nonempty mat (var, vars) failure
  in
  let constrs =
    List.fold_right
      (fun ((c, args), _) acc ->
        if List.mem_assoc c acc then acc else (c, List.length args) :: acc)
      pm_constrs []
  in
  let specialize_pm_constrs c : pm =
    List.filter_map
      (fun ((c', args), (ps, i)) ->
        if c = c' then Some (args @ ps, i) else None)
      pm_constrs
  in
  if constrs = [] then failure
  else
    let num = alloc_trap_code () in
    Lcatch
      ( Lswitch
          ( var,
            List.map
              (fun (c, arity) ->
                ( c,
                  translate (specialize_pm_constrs c)
                    (var_case_accesses arity var @ vars)
                    (Lraise num) ))
              constrs,
            Lraise num ),
        num,
        failure )

and translate_nonempty_not (q, (ps, lam)) mat (var, vars) failure =
  let failure =
    if mat = [] then failure else translate_nonempty mat (var, vars) failure
  in
  let num = alloc_trap_code () in
  let q_mat : pm_nonempty = [ (q, [], Lraise num) ] in
  let q_vars : var_row_nonempty = (var, []) in
  let ps_mat : pm = [ (ps, lam) ] in
  let ps_vars : var_row = vars in
  let body =
    translate_nonempty q_mat q_vars (translate ps_mat ps_vars (Lraise num))
  in
  Lcatch (body, num, failure)

and translate_nonempty_or qs ps mat (var, vars) failure =
  let failure =
    if mat = [] then failure else translate_nonempty mat (var, vars) failure
  in
  let num = alloc_trap_code () in
  let num_fail = alloc_trap_code () in
  let q_mat : pm_nonempty = List.map (fun q -> (q, [], Lraise num)) qs in
  let q_vars : var_row_nonempty = (var, []) in
  let ps_mat : pm = [ ps ] in
  let ps_vars : var_row = vars in
  let body =
    Lcatch
      ( translate_nonempty q_mat q_vars (Lraise num_fail),
        num,
        translate ps_mat ps_vars (Lraise num_fail) )
  in
  Lcatch (body, num_fail, failure)
