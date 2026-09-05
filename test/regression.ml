open Ast
open Interpreter

let failures = ref 0

let test name f =
  try
    f ();
    Printf.printf "PASS %s\n%!" name
  with
  | exn ->
    incr failures;
    Printf.eprintf "FAIL %s: %s\n%!" name (Printexc.to_string exn)
;;

let equal expected actual =
  if expected <> actual
  then
    failwith
      (Printf.sprintf
         "expected %s, got %s"
         (string_of_term expected)
         (string_of_term actual))
;;

let parse s =
  match Parser.parse Parser.parse_term s with
  | Ok t -> t
  | Error e -> failwith e
;;

let strategies =
  [ "CBN", cbn_small_step
  ; "CBV", cbv_small_step
  ; "AO", ao_small_step
  ; "NOR", nor_small_step
  ; "CBN big-step", cbn_big_step
  ]
;;

let () =
  test "substitution must not reuse the substituted variable as a binder" (fun () ->
    let result = subst (var "y'") (var "y") (abs "y" (app (var "y") (var "y'"))) in
    equal (abs "y''" (app (var "y''") (var "y"))) result);
  List.iter
    (fun (name, step) ->
      test (name ^ ": alpha-renaming preserves bound occurrences") (fun () ->
        let term = app (abs "y'" (abs "y" (var "y"))) (var "y") in
        equal (abs "y" (var "y")) (step term)))
    strategies;
  test "substitution does not change a term without the target variable" (fun () ->
    let term = abs "y" (var "y") in
    equal term (subst (var "y'") (var "y") term));
  test "nested binders do not capture fresh variables" (fun () ->
    equal
      (abs "y'" (abs "y''" (app (var "y'") (var "y"))))
      (subst (var "x") (var "y") (abs "y" (abs "y'" (app (var "y") (var "x"))))));
  List.iter
    (fun (source, expected) ->
      test ("parse " ^ source) (fun () -> equal expected (parse source)))
    [ "(a b) c", app (app (var "a") (var "b")) (var "c")
    ; "  x  ", var "x"
    ; "λx.x", abs "x" (var "x")
    ; "\\x.x y", abs "x" (app (var "x") (var "y"))
    ; "(λx.x) y z", app (app (abs "x" (var "x")) (var "y")) (var "z")
    ; "(λx'.x') y", app (abs "x'" (var "x'")) (var "y")
    ; "λx.λy.x y", abs "x" (abs "y" (app (var "x") (var "y")))
    ];
  List.iter
    (fun source ->
      test ("reject " ^ source) (fun () ->
        match Parser.parse Parser.parse_term source with
        | Error _ -> ()
        | Ok t -> failwith ("accepted " ^ string_of_term t)))
    [ "x)"; "x |"; "(x"; "x ("; "(λx.x))"; "" ];
  test "printed alpha-renamed terms round-trip" (fun () ->
    let t = abs "y''" (app (var "y''") (var "y")) in
    equal t (parse (string_of_term t)));
  let redex = app (abs "x" (var "x")) (var "z") in
  List.iter
    (fun (name, step) ->
      test (name ^ ": weak evaluation leaves lambda bodies alone") (fun () ->
        let t = abs "y" redex in
        equal t (step t)))
    [ "CBN", cbn_small_step; "CBV", cbv_small_step; "CBN big-step", cbn_big_step ];
  List.iter
    (fun (name, step) ->
      test (name ^ ": strong evaluation reduces under lambdas") (fun () ->
        equal (abs "y" (var "z")) (step (abs "y" redex))))
    [ "AO", ao_small_step; "NOR", nor_small_step ];
  let omega_abs = abs "x" (app (var "x") (var "x")) in
  let omega = app omega_abs omega_abs in
  List.iter
    (fun (name, step) ->
      test (name ^ ": ignores divergent unused arguments") (fun () ->
        equal (var "z") (step (app (abs "x" (var "z")) omega))))
    [ "CBN", cbn_small_step; "NOR", nor_small_step; "CBN big-step", cbn_big_step ];
  List.iter
    (fun (name, step) ->
      test (name ^ ": evaluates divergent arguments first") (fun () ->
        let t = app (abs "x" (var "z")) omega in
        equal t (step t)))
    [ "CBV", cbv_small_step; "AO", ao_small_step ];
  if !failures <> 0
  then (
    Printf.eprintf "%d failures\n" !failures;
    exit 1)
;;
