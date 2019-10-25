let rec eval_exp env = function
  | Syntax.Lookup loc ->
      List.assoc loc env
  | Syntax.Int n ->
      n
  | Syntax.Plus (exp1, exp2) ->
      eval_exp env exp1 + eval_exp env exp2
  | Syntax.Minus (exp1, exp2) ->
      eval_exp env exp1 - eval_exp env exp2
  | Syntax.Times (exp1, exp2) ->
      eval_exp env exp1 * eval_exp env exp2


let eval_bexp env = function
  | Syntax.Bool b ->
      b
  | Syntax.Equal (exp1, exp2) ->
      eval_exp env exp1 = eval_exp env exp2
  | Syntax.Less (exp1, exp2) ->
      eval_exp env exp1 < eval_exp env exp2
  | Syntax.Greater (exp1, exp2) ->
      eval_exp env exp1 > eval_exp env exp2


let rec eval_cmd env = function
  | Syntax.Assign (l, exp) ->
      let n = eval_exp env exp in
      (l, n) :: List.remove_assoc l env
  | Syntax.IfThenElse (bexp, cmd1, cmd2) ->
      if eval_bexp env bexp then eval_cmd env cmd1 else eval_cmd env cmd2
  | Syntax.Seq (c1, c2) ->
      let env' = eval_cmd env c1 in
      eval_cmd env' c2
  | Syntax.Skip ->
      env
  | Syntax.WhileDo (bexp, cmd) ->
      if eval_bexp env bexp
      then
        let env' = eval_cmd env cmd in
        eval_cmd env' (Syntax.WhileDo (bexp, cmd))
      else env


let print_environment env =
  print_endline "[";
  env
  |> List.sort_uniq (fun (Syntax.Location l, _) (Syntax.Location l', _) ->
         compare l l' )
  |> List.iter (fun (Syntax.Location l, n) ->
         print_endline ("  #" ^ l ^ " := " ^ string_of_int n) );
  print_endline "]"


let run cmd = eval_cmd [] cmd |> print_environment
