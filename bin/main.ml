open Ast
open Interpreter

type strategy =
  { name : string
  ; step : term -> term
  ; reducible : term -> bool
  }

let strategies =
  [ { name = "cbn"; step = cbn_small_step; reducible = is_reducible_in_cbn }
  ; { name = "cbv"; step = cbv_small_step; reducible = is_reducible_in_cbv }
  ; { name = "nor"; step = nor_small_step; reducible = is_reducible_in_nor }
  ; { name = "ao"; step = ao_small_step; reducible = is_reducible_in_ao }
  ]
;;

let strategy = ref (List.nth strategies 2)
let limit = ref 1000
let current = ref None
let original = ref None

let help () =
  print_endline
    "Enter a lambda term to evaluate (λx.x or \\x.x).\n\
     :strategy cbn|cbv|nor|ao  Select reduction strategy (default: nor)\n\
     :steps N                  Set per-run step limit (default: 1000)\n\
     :load TERM                Load without reducing\n\
     :step                     Perform one beta-reduction\n\
     :run                      Continue up to the step limit\n\
     :show                     Show the current term\n\
     :reset                    Restore the original term\n\
     :help                     Show this help\n\
     :quit                     Exit (or send EOF)"
;;

let show () =
  match !current with
  | None -> print_endline "No term loaded."
  | Some term -> print_endline (pretty_term term)
;;

let reduce budget =
  match !current with
  | None -> print_endline "No term loaded."
  | Some term ->
    let rec loop count term =
      if not (!strategy.reducible term)
      then term, count, true
      else if count = budget
      then term, count, false
      else (
        let next = !strategy.step term in
        current := Some next;
        loop (count + 1) next)
    in
    let term, count, done_ = loop 0 term in
    current := Some term;
    print_endline (pretty_term term);
    Printf.printf
      "[%s; %d step(s); %s]\n"
      !strategy.name
      count
      (if done_ then "normal form for strategy" else "step limit reached")
;;

let load source run =
  match Parser.parse Parser.parse_term source with
  | Error _ -> print_endline "Parse error: check the complete expression and parentheses."
  | Ok term ->
    original := Some term;
    current := Some term;
    if run then reduce !limit else show ()
;;

let split_command line =
  let rec find i =
    if i = String.length line
    then line, ""
    else if line.[i] = ' ' || line.[i] = '\t'
    then
      ( String.sub line 0 i
      , String.trim (String.sub line (i + 1) (String.length line - i - 1)) )
    else find (i + 1)
  in
  find 0
;;

let handle line =
  let line = String.trim line in
  if line = ""
  then true
  else if line.[0] <> ':'
  then (
    load line true;
    true)
  else (
    let command, arg = split_command line in
    match command, arg with
    | ":quit", "" -> false
    | ":help", "" ->
      help ();
      true
    | ":show", "" ->
      show ();
      true
    | ":step", "" ->
      reduce 1;
      true
    | ":run", "" ->
      reduce !limit;
      true
    | ":reset", "" ->
      current := !original;
      show ();
      true
    | ":load", source when source <> "" ->
      load source false;
      true
    | ":strategy", "" ->
      print_endline !strategy.name;
      true
    | ":strategy", name ->
      (match List.find_opt (fun s -> s.name = String.lowercase_ascii name) strategies with
       | None -> print_endline "Unknown strategy: use cbn, cbv, nor, or ao."
       | Some s ->
         strategy := s;
         print_endline ("Strategy: " ^ s.name));
      true
    | ":steps", "" ->
      Printf.printf "Step limit: %d\n" !limit;
      true
    | ":steps", value ->
      (match int_of_string_opt value with
       | Some n when n > 0 && n <= 100000 ->
         limit := n;
         Printf.printf "Step limit: %d\n" n
       | _ -> print_endline "Step limit must be an integer from 1 to 100000.");
      true
    | _ ->
      print_endline "Unknown command or invalid arguments. Type :help.";
      true)
;;

let () =
  let interactive = Unix.isatty Unix.stdin in
  if interactive then print_endline "Lambada — type :help for commands.";
  let rec loop () =
    if interactive
    then (
      print_string "lambada> ";
      flush stdout);
    match read_line () with
    | exception End_of_file -> ()
    | line ->
      let continue =
        try handle line with
        | Stack_overflow ->
          print_endline "Expression too deeply nested; load a smaller term or reset.";
          true
      in
      if continue then loop ()
  in
  loop ()
;;
