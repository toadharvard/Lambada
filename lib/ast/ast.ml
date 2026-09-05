(** Copyright 2024, Vadim Yakshigulov *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type term =
  | Var of string
  | Abs of string * term
  | App of term * term
[@@deriving show { with_path = false }, variants]

(* Fully parenthesized output retained for debugging and existing callers. *)
let rec string_of_term = function
  | Var x -> Printf.sprintf "%s" x
  | Abs (x, p) -> Printf.sprintf "(λ%s.%s)" x (string_of_term p)
  | App (p, q) -> Printf.sprintf "(%s %s)" (string_of_term p) (string_of_term q)
;;

(* Abstraction < application < variable; applications associate to the left. *)
let pretty_term term =
  let rec render context = function
    | Var x -> x
    | Abs (x, body) -> wrap (context > 0) ("λ" ^ x ^ "." ^ render 0 body)
    | App (f, arg) -> wrap (context > 1) (render 1 f ^ " " ^ render 2 arg)
  and wrap needed text = if needed then "(" ^ text ^ ")" else text in
  render 0 term
;;
