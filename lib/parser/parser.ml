(** Copyright 2024, Vadim Yakshigulov *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Angstrom
open! Base
open Ast

let ws =
  skip_while (function
    | '\x20' | '\x0a' | '\x0d' | '\x09' -> true
    | _ -> false)
;;

let lparen p = char '(' *> ws *> p
let rparen p = p <* ws <* char ')'

let parse_string =
  take_while1 (function
    | 'a' .. 'z' | 'A' .. 'Z' -> true
    | _ -> false)
;;

let parse_term =
  fix
  @@ fun self ->
  let parse_var = parse_string >>| var in
  let parse_app = lift2 app (lparen self) (ws *> rparen self) in
  let parse_abs =
    lift2
      abs
      (lparen ((string "\\" <|> string "λ") *> ws *> parse_string))
      (rparen (char '.' *> ws *> self))
  in
  choice [ parse_var; parse_app; parse_abs ]
;;

let parse parser str = Angstrom.parse_string ~consume:Consume.Prefix parser str

let parse_show parser show str =
  match parse parser str with
  | Result.Error e -> Format.printf "Error: %s" e
  | Result.Ok ast -> Format.printf "%s\n" (show ast)
;;

let%expect_test _ =
  parse_show parse_term show_term "var";
  [%expect {| (Var "var") |}]
;;

let%expect_test _ =
  parse_show parse_term show_term "(x x)";
  [%expect {| (App ((Var "x"), (Var "x"))) |}]
;;

let%expect_test _ =
  parse_show parse_term show_term {|(\x. x)|};
  [%expect {| (Abs ("x", (Var "x"))) |}]
;;

let%expect_test _ =
  parse_show parse_term show_term {|((\x. x)(\x. x))|};
  [%expect {| (App ((Abs ("x", (Var "x"))), (Abs ("x", (Var "x"))))) |}]
;;
