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
  | RecLambda of ident * ident * exp
  | Apply of exp * exp

let let_in (x, e1, e2) = Apply (Lambda (x, e2), e1)
let let_rec_in (f, x, e1, e2) = let_in (f, RecLambda (f, x, e1), e2)

let rec subst sbst = function
  | Var x as e ->
      begin match List.assoc_opt x sbst with
      | None -> e
      | Some e' -> e'
      end
  | Int _ | Bool _ as e -> e
  | Plus (e1, e2) -> Plus (subst sbst e1, subst sbst e2)
  | Minus (e1, e2) -> Minus (subst sbst e1, subst sbst e2)
  | Times (e1, e2) -> Times (subst sbst e1, subst sbst e2)
  | Equal (e1, e2) -> Equal (subst sbst e1, subst sbst e2)
  | Less (e1, e2) -> Less (subst sbst e1, subst sbst e2)
  | Greater (e1, e2) -> Greater (subst sbst e1, subst sbst e2)
  | IfThenElse (e, e1, e2) -> IfThenElse (subst sbst e, subst sbst e1, subst sbst e2)
  | Lambda (x, e) ->
      let sbst' = List.remove_assoc x sbst in
      Lambda (x, subst sbst' e)
  | RecLambda (f, x, e) ->
      let sbst' = List.remove_assoc f (List.remove_assoc x sbst) in
      RecLambda (f, x, subst sbst' e)
  | Apply (e1, e2) -> Apply (subst sbst e1, subst sbst e2)

let rec string_of_exp3 = function
  | IfThenElse (e, e1, e2) ->
      "IF " ^ string_of_exp2 e ^ " THEN " ^ string_of_exp2 e1 ^ " ELSE " ^ string_of_exp3 e2
  | Lambda (x, e) ->
      "FUN " ^ x ^ " -> " ^ string_of_exp3 e
  | RecLambda (f, x, e) ->
      "REC " ^ f ^ " " ^ x ^ " -> " ^ string_of_exp3 e
  | e -> string_of_exp2 e
and string_of_exp2 = function
  | Equal (e1, e2) ->
    string_of_exp1 e1 ^ " = " ^ string_of_exp1 e2
  | Less (e1, e2) ->
    string_of_exp1 e1 ^ " < " ^ string_of_exp1 e2
  | Greater (e1, e2) ->
    string_of_exp1 e1 ^ " > " ^ string_of_exp1 e2
  | Plus (e1, e2) ->
    string_of_exp1 e1 ^ " + " ^ string_of_exp1 e2
  | Minus (e1, e2) ->
    string_of_exp1 e1 ^ " - " ^ string_of_exp1 e2
  | Times (e1, e2) ->
    string_of_exp1 e1 ^ " * " ^ string_of_exp1 e2
  | e -> string_of_exp1 e
and string_of_exp1 = function
  | Apply (e1, e2) ->
    string_of_exp0 e1 ^ " " ^ string_of_exp0 e2
  | e -> string_of_exp0 e
and string_of_exp0 = function
  | Int n -> string_of_int n
  | Bool b -> if b then "TRUE" else "FALSE"
  | Var x -> x
  | e -> "(" ^ string_of_exp3 e ^ ")"

let string_of_exp = string_of_exp5