type value =
  | Int of int
  | Bool of bool
  | Function of (value -> value)

let string_of_value = function
  | Int n -> string_of_int n
  | Bool b -> if b then "TRUE" else "FALSE"
  | Function _ -> "FUN"


let rec eval_exp env = function
  | Syntax.Var x ->
      (try
        List.assoc x env
      with
        Not_found -> failwith ("NOT FOUND: "^x))
  | Syntax.Int n ->
      Int n
  | Syntax.Plus (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Int (n1 + n2)
  | Syntax.Minus (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Int (n1 - n2)
  | Syntax.Times (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Int (n1 * n2)
  | Syntax.Bool b ->
      Bool b
  | Syntax.Equal (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Bool (n1 = n2)
  | Syntax.Less (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Bool (n1 < n2)
  | Syntax.Greater (e1, e2) ->
      let n1 = eval_int env e1
      and n2 = eval_int env e2
      in Bool (n1 > n2)
  | Syntax.IfThenElse (e, e1, e2) ->
      let b = eval_bool env e in
      eval_exp env (if b then e1 else e2)
  | Syntax.Lambda (x, e) ->
      let func v =
        let env' = (x, v) :: List.remove_assoc x env in
        eval_exp env' e
      in
      Function func
  | Syntax.Apply (e1, e2) ->
      let f = eval_fun env e1
      and v = eval_exp env e2
      in
      f v
  | Syntax.RecLambda (f, x, e) ->
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

let rec subst x v e =
  match e with
  | Syntax.Var x' when x = x' -> v
  | Syntax.Var _ | Syntax.Int _ | Syntax.Bool _ -> e
  | Syntax.Plus (e1, e2) -> Syntax.Plus (subst x v e1, subst x v e2)
  | Syntax.Minus (e1, e2) -> Syntax.Minus (subst x v e1, subst x v e2)
  | Syntax.Times (e1, e2) -> Syntax.Times (subst x v e1, subst x v e2)
  | Syntax.Equal (e1, e2) -> Syntax.Equal (subst x v e1, subst x v e2)
  | Syntax.Less (e1, e2) -> Syntax.Less (subst x v e1, subst x v e2)
  | Syntax.Greater (e1, e2) -> Syntax.Greater (subst x v e1, subst x v e2)
  | Syntax.IfThenElse (e, e1, e2) -> Syntax.IfThenElse (subst x v e, subst x v e1, subst x v e2)
  | Syntax.Lambda (x', _) when x = x' -> e
  | Syntax.Lambda (x', e) -> Syntax.Lambda (x', subst x v e)
  | Syntax.Apply (e1, e2) -> Syntax.Apply (subst x v e1, subst x v e2)
  | Syntax.RecLambda (f', x', _) when f' = x' || x = x' -> e
  | Syntax.RecLambda (f', x', e) -> Syntax.RecLambda (f', x', subst x v e)

exception Stop

let rec step = function
  | Syntax.Var _ | Syntax.Int _ | Syntax.Bool _ | Syntax.Lambda _ | Syntax.RecLambda _ -> raise Stop
  | Syntax.Plus (Syntax.Int n1, Syntax.Int n2) -> Syntax.Int (n1 + n2)
  | Syntax.Plus (Syntax.Int n1, e2) -> Syntax.Plus (Syntax.Int n1, step e2)
  | Syntax.Plus (e1, e2) -> Syntax.Plus (step e1, e2)
  | Syntax.Minus (Syntax.Int n1, Syntax.Int n2) -> Syntax.Int (n1 - n2)
  | Syntax.Minus (Syntax.Int n1, e2) -> Syntax.Minus (Syntax.Int n1, step e2)
  | Syntax.Minus (e1, e2) -> Syntax.Minus (step e1, e2)
  | Syntax.Times (Syntax.Int n1, Syntax.Int n2) -> Syntax.Int (n1 * n2)
  | Syntax.Times (Syntax.Int n1, e2) -> Syntax.Times (Syntax.Int n1, step e2)
  | Syntax.Times (e1, e2) -> Syntax.Times (step e1, e2)
  | Syntax.Equal (Syntax.Int n1, Syntax.Int n2) -> Syntax.Bool (n1 = n2)
  | Syntax.Equal (Syntax.Int n1, e2) -> Syntax.Equal (Syntax.Int n1, step e2)
  | Syntax.Equal (e1, e2) -> Syntax.Equal (step e1, e2)
  | Syntax.Less (Syntax.Int n1, Syntax.Int n2) -> Syntax.Bool (n1 < n2)
  | Syntax.Less (Syntax.Int n1, e2) -> Syntax.Less (Syntax.Int n1, step e2)
  | Syntax.Less (e1, e2) -> Syntax.Less (step e1, e2)
  | Syntax.Greater (Syntax.Int n1, Syntax.Int n2) -> Syntax.Bool (n1 > n2)
  | Syntax.Greater (Syntax.Int n1, e2) -> Syntax.Greater (Syntax.Int n1, step e2)
  | Syntax.Greater (e1, e2) -> Syntax.Greater (step e1, e2)
  | Syntax.IfThenElse (Syntax.Bool b, e1, e2) -> if b then e1 else e2
  | Syntax.IfThenElse (e, e1, e2) -> Syntax.IfThenElse (step e, e1, e2)
  | Syntax.Apply (Syntax.RecLambda (f, x, body) as func, arg) ->
      begin match step_opt arg with
      | Some arg' -> Syntax.Apply (func, arg')
      | None ->
          body
          |> subst f func
          |> subst x arg
      end
  | Syntax.Apply (Syntax.Lambda (x, body) as func, arg) ->
      begin match step_opt arg with
      | Some arg' -> Syntax.Apply (func, arg')
      | None ->
          body
          |> subst x arg
      end
  | Syntax.Apply (e1, e2) -> Syntax.Apply (step e1, e2)
and step_opt e =
  try Some (step e) with Stop -> None

let big_step e =
  let v = eval_exp [] e in
  print_endline (string_of_value v)

let rec small_step e =
  print_endline (Syntax.string_of_exp e);
  match step_opt e with
  | Some e' ->
    print_endline "  -->";
    small_step e'
  | None -> ()
