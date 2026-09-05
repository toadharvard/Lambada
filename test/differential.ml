(* Independent de Bruijn oracle: no named substitution or interpreter predicates. *)
open Ast
open Interpreter

type db =
  | Free of string
  | Bound of int
  | Lam of db
  | Apply of db * db

let rec nameless env = function
  | Var x ->
    let rec find i = function
      | [] -> Free x
      | y :: ys -> if x = y then Bound i else find (i + 1) ys
    in
    find 0 env
  | Abs (x, body) -> Lam (nameless (x :: env) body)
  | App (f, x) -> Apply (nameless env f, nameless env x)
;;

let rec shift delta cutoff = function
  | Bound k when k >= cutoff -> Bound (k + delta)
  | Bound _ as t -> t
  | Free _ as t -> t
  | Lam body -> Lam (shift delta (cutoff + 1) body)
  | Apply (f, x) -> Apply (shift delta cutoff f, shift delta cutoff x)
;;

let beta body arg =
  let rec replace depth = function
    | Bound k when k = depth -> shift depth 0 (shift 1 0 arg)
    | Bound _ as t -> t
    | Free _ as t -> t
    | Lam b -> Lam (replace (depth + 1) b)
    | Apply (f, x) -> Apply (replace depth f, replace depth x)
  in
  shift (-1) 0 (replace 0 body)
;;

let rec reference strategy = function
  | Free _ | Bound _ -> None
  | Lam body ->
    if strategy = "AO" || strategy = "NOR"
    then Option.map (fun b -> Lam b) (reference strategy body)
    else None
  | Apply (Lam body, arg) when strategy = "CBN" || strategy = "NOR" ->
    Some (beta body arg)
  | Apply (f, arg) ->
    (match reference strategy f with
     | Some f' -> Some (Apply (f', arg))
     | None ->
       if strategy = "CBN"
       then None
       else (
         match reference strategy arg with
         | Some arg' -> Some (Apply (f, arg'))
         | None ->
           (match f with
            | Lam body -> Some (beta body arg)
            | _ -> None)))
;;

let strategies =
  [ "CBN", cbn_small_step, is_reducible_in_cbn
  ; "CBV", cbv_small_step, is_reducible_in_cbv
  ; "AO", ao_small_step, is_reducible_in_ao
  ; "NOR", nor_small_step, is_reducible_in_nor
  ]
;;

let rng = Random.State.make [| 2024; 905 |]
let names = [| "x"; "y"; "z"; "x'"; "y'"; "x''" |]
let name () = names.(Random.State.int rng (Array.length names))

let rec generate depth =
  if depth = 0
  then var (name ())
  else (
    match Random.State.int rng 4 with
    | 0 -> var (name ())
    | 1 ->
      let x = name () in
      abs x (generate (depth - 1))
    | _ ->
      let f = generate (depth - 1) in
      app f (generate (depth - 1)))
;;

let check term =
  let db = nameless [] term in
  List.iter
    (fun print ->
      match Parser.parse Parser.parse_term (print term) with
      | Ok parsed when parsed = term -> ()
      | _ -> failwith ("round-trip failed: " ^ print term))
    [ string_of_term; pretty_term ];
  List.iter
    (fun (strategy, step, reducible) ->
      let expected = reference strategy db in
      if reducible term <> Option.is_some expected
      then failwith (strategy ^ " reducibility mismatch: " ^ string_of_term term);
      let expected = Option.value expected ~default:db in
      if nameless [] (step term) <> expected
      then failwith (strategy ^ " step mismatch: " ^ string_of_term term);
      (* Follow bounded traces, including nonterminating terms, without big-step hangs. *)
      let rec trace fuel t d =
        if fuel = 0
        then ()
        else (
          match reference strategy d with
          | None ->
            if reducible t then failwith (strategy ^ " terminal predicate mismatch");
            if strategy = "CBN" && nameless [] (cbn_big_step term) <> d
            then failwith "CBN big/small-step mismatch"
          | Some d' ->
            let t' = step t in
            if nameless [] t' <> d'
            then failwith (strategy ^ " trace mismatch: " ^ string_of_term term);
            trace (fuel - 1) t' d')
      in
      trace 8 term db)
    strategies
;;

let () =
  for _ = 1 to 10000 do
    check (generate 5)
  done;
  Printf.printf
    "PASS 10000 generated terms: parser round-trips, four strategy oracles,\n\
     reducibility, bounded traces, and terminating CBN big/small-step agreement\n"
;;
