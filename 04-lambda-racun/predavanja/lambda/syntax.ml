type ident = string

type exp =
  | Var of ident
  | Int of int
  | Plus of exp * exp
  | Minus of exp * exp
  | Times of exp * exp
  | Bool of bool
  | Equal of exp * exp
  | Less of exp * exp
  | Greater of exp * exp
  | IfThenElse of exp * exp * exp
  | Lambda of ident * exp
  | Apply of exp * exp
  | RecLambda of ident * ident * exp

let rec string_of_exp5 = function
  | IfThenElse (e, e1, e2) ->
      "IF " ^ string_of_exp4 e ^ " THEN " ^ string_of_exp4 e1 ^ " ELSE " ^ string_of_exp5 e2
  | Lambda (x, e) ->
      "FUN " ^ x ^ " -> " ^ string_of_exp5 e
  | RecLambda (f, x, e) ->
      "REC " ^ f ^ " " ^ x ^ " -> " ^ string_of_exp5 e
  | e -> string_of_exp4 e
and string_of_exp4 = function
  | Equal (e1, e2) ->
    string_of_exp3 e1 ^ " = " ^ string_of_exp3 e2
  | Less (e1, e2) ->
    string_of_exp3 e1 ^ " < " ^ string_of_exp3 e2
  | Greater (e1, e2) ->
    string_of_exp3 e1 ^ " > " ^ string_of_exp3 e2
  | e -> string_of_exp3 e
and string_of_exp3 = function
  | Plus (e1, e2) ->
    string_of_exp2 e1 ^ " + " ^ string_of_exp3 e2
  | Minus (e1, e2) ->
    string_of_exp2 e1 ^ " - " ^ string_of_exp2 e2
  | e -> string_of_exp2 e
and string_of_exp2 = function
  | Times (e1, e2) ->
    string_of_exp1 e1 ^ " * " ^ string_of_exp2 e2
  | e -> string_of_exp1 e
and string_of_exp1 = function
  | Apply (e1, e2) ->
    string_of_exp1 e1 ^ " " ^ string_of_exp0 e2
  | e -> string_of_exp0 e
and string_of_exp0 = function
  | Int n -> string_of_int n
  | Bool b -> if b then "TRUE" else "FALSE"
  | Var x -> x
  | e -> "(" ^ string_of_exp5 e ^ ")"

let string_of_exp = string_of_exp5