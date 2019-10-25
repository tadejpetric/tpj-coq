type value =
  | Int of int
  | Bool of bool
  | Function of (value -> value)

let print_value = function
  | Int n -> print_endline ("Int " ^ string_of_int n)
  | Bool b -> print_endline ("Bool " ^ string_of_bool b)
  | Function _ -> print_endline ("Function <fun>")


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

let eval e = eval_exp [("is_zero", Function (fun (Int n) -> Bool (n = 0)))] e |> print_value
