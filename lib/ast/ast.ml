(** Copyright 2024, Vadim Yakshigulov *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type term =
  | Var of string
  | Abs of string * term
  | App of term * term
[@@deriving show { with_path = false }, variants]

let rec string_of_term = function
  | Var x -> Printf.sprintf "%s" x
  | Abs (x, p) -> Printf.sprintf "(λ%s.%s)" x (string_of_term p)
  | App (p, q) -> Printf.sprintf "(%s %s)" (string_of_term p) (string_of_term q)
;;
