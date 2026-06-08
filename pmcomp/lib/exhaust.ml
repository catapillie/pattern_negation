open Ast

type env = Ast.sigdef list
type row = pat list
type row_nonempty = pat * pat list
type contra = row list
type contra_nonempty = row_nonempty list

let display_contra (mat : contra) =
  List.map
    (fun row ->
      Printf.sprintf "%d| %s" (List.length row)
        (List.map display_pat row |> String.concat "\t"))
    mat
  |> String.concat "\n"

let omegas k = List.init k (fun _ -> Pomega)
let to_nonempty_mat = List.map (fun row -> (List.hd row, List.tl row))

let filter_mapi f =
  let rec build i = function
    | [] -> []
    | x :: xs -> (
        match f i x with
        | Some y -> y :: build (i + 1) xs
        | None -> build (i + 1) xs)
  in
  build 0

let cartesian2 l l' =
  List.concat_map (fun e -> List.map (fun e' -> (e, e')) l') l

let rec specialize ((c, arity) : string * int) (mat : contra_nonempty) : contra
    =
  (* print_endline ("spec " ^ c); *)
  List.fold_right
    (fun (p1, ps) acc ->
      match p1 with
      | Pomega -> (omegas arity @ ps) :: acc
      | Pconstr (c', args) when c = c' -> (args @ ps) :: acc
      | Pconstr _ -> acc
      | Por (r1, r2) -> specialize (c, arity) [ (r1, ps); (r2, ps) ] @ acc
      | Pand (r1, r2) ->
          inter_contra
            (specialize (c, arity) [ (r1, ps) ])
            (specialize (c, arity) [ (r2, ps) ])
      | Pnot q -> (
          match q with
          | Pnot r -> specialize (c, arity) [ (r, ps) ] @ acc
          | Pomega -> acc
          | Pconstr (c', args) when c = c' ->
              let truc =
                filter_mapi
                  (fun i arg ->
                    match arg with
                    | Pomega -> None
                    | Pnot r ->
                        Some
                          (List.init arity (fun j ->
                               if i = j then r else Pomega))
                    | p ->
                        Some
                          (List.init arity (fun j ->
                               if i = j then Pnot p else Pomega)))
                  args
              in
              List.map (fun neg_args -> neg_args @ ps) truc @ acc
          | Pconstr (c', args) -> (omegas arity @ ps) :: acc
          | Pand (r1, r2) -> specialize (c, arity) [ (r1, ps); (r2, ps) ] @ acc
          | Por (r1, r2) ->
              inter_contra
                (specialize (c, arity) [ (Pnot r1, ps) ])
                (specialize (c, arity) [ (Pnot r2, ps) ])
              @ acc))
    mat []

and inter_contra (m1 : contra) (m2 : contra) : contra =
  cartesian2 m1 m2 |> List.filter_map inter_row

and inter_row (r1, r2) : row option =
  List.fold_right
    (fun p1p2 acc ->
      match (inter_pat p1p2, acc) with
      | Some p, Some acc -> Some (p :: acc)
      | _ -> None)
    (List.combine r1 r2) (Some [])

and inter_pat = function
  | p, Pomega | Pomega, p -> Some p
  | Pnot p1, Pnot p2 -> Some (Pnot (Por (p1, p2)))
  | Pconstr (c1, args1), Pconstr (c2, args2) ->
      if c1 = c2 then
        Option.map (fun args -> Pconstr (c1, args)) (inter_row (args1, args2))
      else None
  | p1, p2 -> if p1 = p2 then Some p1 else Some (Pand (p1, p2))

let rec specialize_default = specialize ("<?>", 0)

let check_complete (sa : string list) (env : env) =
  List.exists
    (fun (Sig sb) ->
      List.for_all (fun ca -> List.mem ca sb) sa
      && List.for_all (fun cb -> List.mem cb sa) sb)
    env

let rec collect_column_signature (mat : contra_nonempty) : (string * int) list =
  List.fold_left (fun acc (p, _) -> collect_pattern_signature acc p) [] mat

and collect_pattern_signature acc (p : pat) : (string * int) list =
  match p with
  | Pomega -> acc
  | Pconstr (c, args) ->
      if List.mem_assoc c acc then acc else (c, List.length args) :: acc
  | Por (r1, r2) | Pand (r1, r2) ->
      let acc = collect_pattern_signature acc r2 in
      let acc = collect_pattern_signature acc r1 in
      acc
  | Pnot p -> collect_pattern_signature acc p

let rec sat (mat : contra) (q : row) (env : env) : bool =
  (* print_endline "sat";
  print_endline (display_contra mat);
  print_endline "--------------";
  print_endline (display_contra [ q ]);
  print_newline (); *)
  match mat with
  | [] -> true
  | _ -> (
      match q with
      | [] -> false
      | q1 :: qs -> sat_nonempty (to_nonempty_mat mat) (q1, qs) env)

and sat_nonempty (mat : contra_nonempty) ((q1, qs) : row_nonempty) (env : env) :
    bool =
  match q1 with
  | Pomega ->
      let constrs = collect_column_signature mat in
      let is_complete = check_complete (List.map fst constrs) env in
      if is_complete then sat_omega_complete mat qs constrs env
      else sat_omega_incomplete mat qs constrs env
  | Pconstr (c, args) ->
      let arity = List.length args in
      let spec_row = args @ qs in
      let spec_mat = specialize (c, arity) mat in
      sat spec_mat spec_row env
  | Por (r1, r2) ->
      sat_nonempty mat (r1, qs) env || sat_nonempty mat (r2, qs) env
  | Pand (r1, r2) ->
      sat_nonempty mat (r1, qs) env && sat_nonempty mat (r2, qs) env
  | Pnot r ->
      let new_row = (r, qs) in
      let new_mat = mat @ [ new_row ] in
      sat_nonempty new_mat (Pomega, qs) env

and sat_omega_complete (mat : contra_nonempty) (qs : row)
    (constrs : (string * int) list) (env : env) =
  List.exists
    (fun (c, arity) ->
      let spec_row = omegas arity @ qs in
      let spec_mat = specialize (c, arity) mat in
      sat spec_mat spec_row env)
    constrs

and sat_omega_incomplete (mat : contra_nonempty) (qs : row)
    (constrs : (string * int) list) (env : env) =
  List.exists
    (fun (c, arity) ->
      let spec_row = omegas arity @ qs in
      let spec_mat = specialize (c, arity) mat in
      sat spec_mat spec_row env)
    constrs
  ||
  let spec_row = qs in
  let spec_mat = specialize_default mat in
  sat spec_mat spec_row env

let is_partial (pm : pat list) (env : env) : bool =
  let mat = List.map (fun p -> [ p ]) pm in
  let row = [ Pomega ] in
  sat mat row env
