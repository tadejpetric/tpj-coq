module S = Syntax

type value =
  | Int of int
  | Bool of bool
  | Function of (value -> value)

let string_of_value = function
  | Int n -> string_of_int n
  | Bool b -> if b then "TRUE" else "FALSE"
  | Function _ -> "FUN"


let rec eval_exp env = function
  | S.Var x -> List.assoc x env
  | S.Int n ->
      Int n
  | S.Plus (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Int (n1 + n2)
  | S.Minus (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Int (n1 - n2)
  | S.Times (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Int (n1 * n2)
  | S.Bool b ->
      Bool b
  | S.Equal (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Bool (n1 = n2)
  | S.Less (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Bool (n1 < n2)
  | S.Greater (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Bool (n1 > n2)
  | S.IfThenElse (e, e1, e2) ->
      let b = eval_bool env e in
      eval_exp env (if b then e1 else e2)
  | S.Lambda (x, e) ->
      let func v =
        let env' = (x, v) :: List.remove_assoc x env in
        eval_exp env' e
      in
      Function func
  | S.Apply (e1, e2) ->
      let f = eval_fun env e1
      and v = eval_exp env e2
      in
      f v
  | S.RecLambda (f, x, e) ->
      let rec func v =
        let env' = (x, v) :: (f, Function func) :: List.remove_assoc x env in
        eval_exp env' e
      in
      Function func
and eval_int env e =
  match eval_exp env e with
  | Int n -> n
  | _ -> failwith "Integer expected"
and eval_bool env e =
  match eval_exp env e with
  | Bool n -> n
  | _ -> failwith "Boolean expected"
and eval_fun env e =
  match eval_exp env e with
  | Function f -> f
  | _ -> failwith "Function expected"

let is_value = function
  | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ -> true
  | S.Var _ | S.Plus _ | S.Minus _ | S.Times _ | S.Equal _ | S.Less _ | S.Greater _
  | S.IfThenElse _ | S.Apply _ -> false

let rec step = function
  | S.Var _ | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ -> failwith "Expected a non-terminal expression"
  | S.Plus (S.Int n1, S.Int n2) -> S.Int (n1 + n2)
  | S.Plus (S.Int n1, e2) -> S.Plus (S.Int n1, step e2)
  | S.Plus (e1, e2) -> S.Plus (step e1, e2)
  | S.Minus (S.Int n1, S.Int n2) -> S.Int (n1 - n2)
  | S.Minus (S.Int n1, e2) -> S.Minus (S.Int n1, step e2)
  | S.Minus (e1, e2) -> S.Minus (step e1, e2)
  | S.Times (S.Int n1, S.Int n2) -> S.Int (n1 * n2)
  | S.Times (S.Int n1, e2) -> S.Times (S.Int n1, step e2)
  | S.Times (e1, e2) -> S.Times (step e1, e2)
  | S.Equal (S.Int n1, S.Int n2) -> S.Bool (n1 = n2)
  | S.Equal (S.Int n1, e2) -> S.Equal (S.Int n1, step e2)
  | S.Equal (e1, e2) -> S.Equal (step e1, e2)
  | S.Less (S.Int n1, S.Int n2) -> S.Bool (n1 < n2)
  | S.Less (S.Int n1, e2) -> S.Less (S.Int n1, step e2)
  | S.Less (e1, e2) -> S.Less (step e1, e2)
  | S.Greater (S.Int n1, S.Int n2) -> S.Bool (n1 > n2)
  | S.Greater (S.Int n1, e2) -> S.Greater (S.Int n1, step e2)
  | S.Greater (e1, e2) -> S.Greater (step e1, e2)
  | S.IfThenElse (S.Bool b, e1, e2) -> if b then e1 else e2
  | S.IfThenElse (e, e1, e2) -> S.IfThenElse (step e, e1, e2)
  | S.Apply (S.Lambda (x, e), v) when is_value v -> S.subst [(x, v)] e
  | S.Apply (S.RecLambda (f, x, e) as rec_f, v) when is_value v -> S.subst [(f, rec_f); (x, v)] e
  | S.Apply ((S.Lambda _ | S.RecLambda _) as f, e) -> S.Apply (f, step e)
  | S.Apply (e1, e2) -> S.Apply (step e1, e2)

let big_step e =
  let v = eval_exp [] e in
  print_endline (string_of_value v)

let rec small_step e =
  print_endline (S.string_of_exp e);
  if not (is_value e) then
    (print_endline "  -->";
    small_step (step e))
