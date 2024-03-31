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
let parens p = char '(' *> ws *> p <* ws <* char ')'

let parse_string =
  take_while1 (function
    | 'a' .. 'z' | 'A' .. 'Z' -> true
    | _ -> false)
;;

let lambda_sym = string "\\" <|> string "λ"

let parse_term =
  fix
  @@ fun self ->
  let parse_var = parse_string >>| var in
  let parse_abs =
    fix
    @@ fun parse_abs ->
    lift2 abs (lambda_sym *> ws *> parse_string) (char '.' *> ws *> (parse_abs <|> self))
  in
  let parse_app =
    lift2 app (lparen self) (ws *> rparen self)
    <|> (sep_by1 ws (choice [ parens parse_abs; parens self; parse_var ])
         >>= function
         | x :: xs -> return @@ List.fold_left ~f:app ~init:x xs
         | _ -> fail "Impossible state")
  in
  parse_app
;;

let parse parser str = Angstrom.parse_string ~consume:Consume.Prefix parser str

let parse_show parser show str =
  match parse parser str with
  | Result.Error e -> Format.printf "Error: %s" e
  | Result.Ok ast -> Format.printf "%s\n" (show ast)
;;

let%expect_test _ =
  parse_show parse_term show_term "Var";
  [%expect {| (Var "Var") |}]
;;

let%expect_test _ =
  parse_show parse_term show_term "Var x";
  [%expect {| (App ((Var "Var"), (Var "x"))) |}]
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

(* CBV: factorial *)
let%expect_test _ =
  parse_show
    parse_term
    show_term
    {|(λf. λn. (iszero n) (λp. ONE) (λp. mult n (f (pred n))) unused)|};
  [%expect
    {|
      (Abs ("f",
         (Abs ("n",
            (App (
               (App (
                  (App ((App ((Var "iszero"), (Var "n"))), (Abs ("p", (Var "ONE")))
                     )),
                  (Abs ("p",
                     (App ((App ((Var "mult"), (Var "n"))),
                        (App ((Var "f"), (App ((Var "pred"), (Var "n")))))))
                     ))
                  )),
               (Var "unused")))
            ))
         ))
    |}]
;;

(* Z-combinator *)
let%expect_test _ =
  parse_show parse_term show_term {|(λf. (λx. f (λv. x x v))  (λx. f (λv. x x v)) )|};
  [%expect
    {|
      (Abs ("f",
         (App (
            (Abs ("x",
               (App ((Var "f"),
                  (Abs ("v", (App ((App ((Var "x"), (Var "x"))), (Var "v")))))))
               )),
            (Abs ("x",
               (App ((Var "f"),
                  (Abs ("v", (App ((App ((Var "x"), (Var "x"))), (Var "v")))))))
               ))
            ))
         ))
    |}]
;;

(* NO: iszero (pred 1)*)
let%expect_test _ =
  parse_show
    parse_term
    show_term
    {|(λn. n (λp. (λx.λy.y)) (λx.λy.x))((λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (λu. u))(λs. λz. s z))|};
  [%expect
    {|
    (App (
       (Abs ("n",
          (App (
             (App ((Var "n"), (Abs ("p", (Abs ("x", (Abs ("y", (Var "y"))))))))),
             (Abs ("x", (Abs ("y", (Var "x")))))))
          )),
       (App (
          (Abs ("n",
             (Abs ("f",
                (Abs ("x",
                   (App (
                      (App (
                         (App ((Var "n"),
                            (Abs ("g",
                               (Abs ("h",
                                  (App ((Var "h"), (App ((Var "g"), (Var "f")))))
                                  ))
                               ))
                            )),
                         (Abs ("u", (Var "x"))))),
                      (Abs ("u", (Var "u")))))
                   ))
                ))
             )),
          (Abs ("s", (Abs ("z", (App ((Var "s"), (Var "z")))))))))
       ))
    |}]
;;
