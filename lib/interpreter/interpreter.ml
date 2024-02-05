(** Copyright 2024, Vadim Yakshigulov *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)
open Parser

open Ast
module StringSet = Set.Make (String)

let get_free_vars =
  let rec helper acc = function
    | Var s -> StringSet.add s acc
    | Abs (s, l) -> StringSet.union acc (StringSet.remove s (helper StringSet.empty l))
    | App (l, r) -> helper (helper acc r) l
  in
  helper StringSet.empty
;;

let is_free var in_term =
  let free_vars = get_free_vars in_term in
  StringSet.mem var free_vars
;;

let rec next_name old free_vars : string =
  if StringSet.mem old free_vars then next_name (old ^ "'") free_vars else old
;;

let rec subst var_to_replace repacement term =
  match var_to_replace, repacement, term with
  | Var x, n, Var x' when String.equal x x' -> n
  (* [x -> N] x = N *)
  | Var x, _n, Var y when not (String.equal x y) -> var y
  (* [x -> N] y = y *)
  | x, n, App (p, q) -> app (subst x n p) (subst x n q)
  (* [x -> N] (P Q) = ([x -> N] P)([x -> N] Q) *)
  | Var x, _n, Abs (x', p) when String.equal x x' -> abs x' p
  (* [x -> N] (λx. P) = (λx. P) *)
  | Var x, n, Abs (y, p) when (not (String.equal x y)) && is_free y n ->
    let free_vars = StringSet.union (get_free_vars n) (get_free_vars p) in
    let z = next_name x free_vars in
    abs z (subst (Var x) n (subst (Var y) (Var z) p))
  (* [x -> N] (λx. P) = (λz. [x -> N] ([y -> z] P)) if y in FV(N) *)
  | Var x, n, Abs (y, p) when (not (String.equal x y)) && not (is_free y n) ->
    abs y (subst (Var x) n p)
  (* [x -> N] (λx. P) = (λy. [x -> N] P) if y not in FV(N) *)
  | _, _, _ -> failwith "Unable to complete substitution"
;;

let rec cbn_big_step = function
  | Var x -> var x
  | Abs (x, e) -> abs x e
  | App (e1, e2) ->
    let e1' = cbn_big_step e1 in
    (match e1' with
     | Abs (x, e) ->
       let e' = cbn_big_step (subst (var x) e2 e) in
       e'
     | _ -> app e1' e2)
;;

(* Inspired by https://groups.seas.harvard.edu/courses/cs152/2021sp/lectures/sld07-lambdacalc.pdf *)
let rec is_reducible_in_cbv = function
  | Var _x -> false
  | Abs (_x, _e) -> false
  | App (Abs (_x, _e), v) when not (is_reducible_in_cbv v) -> true
  | App (v, e) when not (is_reducible_in_cbv v) -> is_reducible_in_cbv e
  | App (e1, _e2) -> is_reducible_in_cbv e1
;;

let rec cbv_small_step = function
  | Var x -> var x
  | Abs (x, e) -> abs x e
  | App (Abs (x, e), v) when not (is_reducible_in_cbv v) -> subst (var x) v e
  | App (v, e) when not (is_reducible_in_cbv v) ->
    let e' = cbv_small_step e in
    app v e'
  | App (e1, e2) ->
    let e1' = cbv_small_step e1 in
    app e1' e2
;;

let rec is_reducible_in_ao = function
  | Var _x -> false
  | Abs (_x, e) -> is_reducible_in_ao e
  | App (Abs (_x, _e), v) when not (is_reducible_in_ao v) -> true
  | App (v, e) when not (is_reducible_in_ao v) -> is_reducible_in_ao e
  | App (e1, _e2) -> is_reducible_in_ao e1
;;

let rec ao_small_step = function
  | Var x -> var x
  | Abs (x, e) ->
    let e' = ao_small_step e in
    abs x e'
  | App (Abs (x, e), v) when not (is_reducible_in_ao v) -> subst (var x) v e
  | App (v, e) when not (is_reducible_in_ao v) ->
    let e' = ao_small_step e in
    app v e'
  | App (e1, e2) ->
    let e1' = ao_small_step e1 in
    app e1' e2
;;

let rec cbn_small_step = function
  | Var x -> var x
  | Abs (x, e) -> abs x e
  | App (Abs (x, e1), e2) -> subst (var x) e2 e1
  | App (e1, e2) ->
    let e1' = cbn_small_step e1 in
    app e1' e2
;;

let rec nor_small_step = function
  | Var x -> var x
  | Abs (x, e) ->
    let e' = nor_small_step e in
    abs x e'
  | App (Abs (x, e), e') -> subst (var x) e' e
  | App (Var x, e) ->
    let e' = nor_small_step e in
    app (var x) e'
  | App (e1, e2) ->
    let e1' = cbn_small_step e1 in
    app e1' e2
;;

(* Tests *)
let rec apply_n_times f x n = if n <= 0 then x else apply_n_times f (f x) (n - 1)

let iterpret ?(show = string_of_term) strat term_string n =
  match parse parse_term term_string with
  | Result.Error _ -> Format.printf "Can't parse expression, double check parens"
  | Result.Ok term -> Format.printf "Out: %s \n" (show (apply_n_times strat term n))
;;

let%expect_test _ =
  (* (λx.(λy.y))Ω cbv -> расходится*)
  iterpret cbv_small_step {|((λx.(λy.y)) ((λx.(x x)) (λy.(y y))))|} 1;
  [%expect {| Out: ((λx.(λy.y)) ((λy.(y y)) (λy.(y y)))) |}]
;;

let%expect_test _ =
  (* CBV почти завершился для Z fac 1, шаг 33*)
  let term =
    {|(((λf. ((λx. (f (λv. ((x x) v)))) (λx. (f (λv. ((x x) v)))))) (λf. (λn. (((((λn.((n (λp. (λx.(λy.y)))) (λx.(λy.x)))) n) (λp. (λs. (λz. (s z))))) (λp.(((λm. (λn. ((m ((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) n)) (λs. (λz. z))))) n) (f ((λn. (λf.( λx. (((n (λg. (λh. (h (g f))))) (λu. x)) (λu. u))))) n))))) unused)))) (λs. (λz. (s z))))  |}
  in
  iterpret cbv_small_step term 33;
  [%expect {| Out: ((λn.(λf.(λx.(((λs.(λz.(s z))) f) ((n f) x))))) (λs.(λz.z))) |}]
;;

let%expect_test _ =
  (* CBV завершился для Z fac 1, шаг 34*)
  let term =
    {|(((λf. ((λx. (f (λv. ((x x) v)))) (λx. (f (λv. ((x x) v)))))) (λf. (λn. (((((λn.((n (λp. (λx.(λy.y)))) (λx.(λy.x)))) n) (λp. (λs. (λz. (s z))))) (λp.(((λm. (λn. ((m ((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) n)) (λs. (λz. z))))) n) (f ((λn. (λf.( λx. (((n (λg. (λh. (h (g f))))) (λu. x)) (λu. u))))) n))))) unused)))) (λs. (λz. (s z))))  |}
  in
  iterpret cbv_small_step term 34;
  [%expect {| Out: (λf.(λx.(((λs.(λz.(s z))) f) (((λs.(λz.z)) f) x)))) |}]
;;

let%expect_test _ =
  (* Досчитаем в AO*)
  let term = {|(λf.(λx.(((λs.(λz.(s z))) f) (((λs.(λz.z)) f) x))))|} in
  iterpret ao_small_step term 100;
  [%expect {|
        Out: (λf.(λx.(f x))) |}]
;;

let%expect_test _ =
  (* AO расходится *)
  let term =
    {|(((λf. ((λx. (f (λv. ((x x) v)))) (λx. (f (λv. ((x x) v)))))) (λf. (λn. (((((λn.((n (λp. (λx.(λy.y)))) (λx.(λy.x)))) n) (λp. (λs. (λz. (s z))))) (λp.(((λm. (λn. ((m ((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) n)) (λs. (λz. z))))) n) (f ((λn. (λf.( λx. (((n (λg. (λh. (h (g f))))) (λu. x)) (λu. u))))) n))))) unused)))) (λs. (λz. (s z))))  |}
  in
  iterpret ao_small_step term 20;
  [%expect
    {| Out: (((λf.(f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.((f (λv.(((λx.(f (λv.((x x) v)))) (λx.(f (λv.((x x) v))))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v))) v)))) (λf.(λn.(((((λn.((n (λp.(λx.(λy.y)))) (λx.(λy.x)))) n) (λp.(λs.(λz.(s z))))) (λp.(((λm.(λn.((m ((λm.(λn.(λf.(λx.((m f) ((n f) x)))))) n)) (λs.(λz.z))))) n) (f ((λn.(λf.(λx.(((n (λg.(λh.(h (g f))))) (λu.x)) (λu.u))))) n))))) unused)))) (λs.(λz.(s z)))) |}]
;;

let%expect_test _ =
  (* (λx.(λy.y))Ω cbn -> (λy.y) *)
  iterpret ~show:show_term cbn_small_step {|((λx.(λy.y)) ((λx.(x x)) (λy.(y y))))|} 2;
  [%expect {| Out: (Abs ("y", (Var "y"))) |}]
;;

let%expect_test _ =
  (* CBN завершился для Z fac 1, шаг 17, но размер -- мое почтение*)
  let term =
    {|(((λf. ((λx. (f (λv. ((x x) v)))) (λx. (f (λv. ((x x) v)))))) (λf. (λn. (((((λn.((n (λp. (λx.(λy.y)))) (λx.(λy.x)))) n) (λp. (λs. (λz. (s z))))) (λp.(((λm. (λn. ((m ((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) n)) (λs. (λz. z))))) n) (f ((λn. (λf.( λx. (((n (λg. (λh. (h (g f))))) (λu. x)) (λu. u))))) n))))) unused)))) (λs. (λz. (s z))))  |}
  in
  iterpret cbn_small_step term 100000;
  [%expect
    {| Out: (λf.(λx.((((λv.(((λx.((λf.(λn.(((((λn.((n (λp.(λx.(λy.y)))) (λx.(λy.x)))) n) (λp.(λs.(λz.(s z))))) (λp.(((λm.(λn.((m ((λm.(λn.(λf.(λx.((m f) ((n f) x)))))) n)) (λs.(λz.z))))) n) (f ((λn.(λf.(λx.(((n (λg.(λh.(h (g f))))) (λu.x)) (λu.u))))) n))))) unused))) (λv.((x x) v)))) (λx.((λf.(λn.(((((λn.((n (λp.(λx.(λy.y)))) (λx.(λy.x)))) n) (λp.(λs.(λz.(s z))))) (λp.(((λm.(λn.((m ((λm.(λn.(λf.(λx.((m f) ((n f) x)))))) n)) (λs.(λz.z))))) n) (f ((λn.(λf.(λx.(((n (λg.(λh.(h (g f))))) (λu.x)) (λu.u))))) n))))) unused))) (λv.((x x) v))))) v)) ((λn.(λf.(λx.(((n (λg.(λh.(h (g f))))) (λu.x)) (λu.u))))) (λs.(λz.(s z))))) f) (((λs.(λz.z)) f) x)))) |}]
;;

let%expect_test "cbn_ybc" =
  let term = {|((λx.((λz.(z x)) y)) ((λt.(b t)) c))|} in
  iterpret cbn_small_step term 0;
  iterpret cbn_small_step term 1;
  iterpret cbn_small_step term 2;
  iterpret cbn_big_step term 1;
  [%expect
    {|
    Out: ((λx.((λz.(z x)) y)) ((λt.(b t)) c))
    Out: ((λz.(z ((λt.(b t)) c))) y)
    Out: (y ((λt.(b t)) c))
    Out: (y ((λt.(b t)) c)) |}]
;;

let%expect_test "cbv_ybc" =
  let term = {|((λx.((λz.(z x)) y)) ((λt.(b t)) c))|} in
  iterpret cbv_small_step term 0;
  iterpret cbv_small_step term 1;
  iterpret cbv_small_step term 2;
  iterpret cbv_small_step term 3;
  [%expect
    {|
      Out: ((λx.((λz.(z x)) y)) ((λt.(b t)) c))
      Out: ((λx.((λz.(z x)) y)) (b c))
      Out: ((λz.(z (b c))) y)
      Out: (y (b c)) |}]
;;

let%expect_test "ao_ybc" =
  let term = {|((λx.((λz.(z x)) y)) ((λt.(b t)) c))|} in
  iterpret ao_small_step term 0;
  iterpret ao_small_step term 1;
  iterpret ao_small_step term 2;
  iterpret ao_small_step term 3;
  [%expect
    {|
        Out: ((λx.((λz.(z x)) y)) ((λt.(b t)) c))
        Out: ((λx.(y x)) ((λt.(b t)) c))
        Out: ((λx.(y x)) (b c))
        Out: (y (b c)) |}]
;;

let%expect_test "nor_ybc" =
  let term = {|((λx.((λz.(z x)) y)) ((λt.(b t)) c))|} in
  iterpret nor_small_step term 0;
  iterpret nor_small_step term 1;
  iterpret nor_small_step term 2;
  iterpret nor_small_step term 3;
  [%expect
    {|
          Out: ((λx.((λz.(z x)) y)) ((λt.(b t)) c))
          Out: ((λz.(z ((λt.(b t)) c))) y)
          Out: (y ((λt.(b t)) c))
          Out: (y (b c)) |}]
;;
