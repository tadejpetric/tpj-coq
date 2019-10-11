let rec check_exp locs = function
  | Syntax.Lookup loc ->
      List.mem loc locs
  | Syntax.Int _ ->
      true
  | Syntax.Plus (exp1, exp2) ->
      check_exp locs exp1 && check_exp locs exp2
  | Syntax.Minus (exp1, exp2) ->
      check_exp locs exp1 && check_exp locs exp2
  | Syntax.Times (exp1, exp2) ->
      check_exp locs exp1 && check_exp locs exp2


let check_bexp locs = function
  | Syntax.Bool b ->
      true
  | Syntax.Equal (exp1, exp2) ->
      check_exp locs exp1 && check_exp locs exp2
  | Syntax.Less (exp1, exp2) ->
      check_exp locs exp1 && check_exp locs exp2
  | Syntax.Greater (exp1, exp2) ->
      check_exp locs exp1 && check_exp locs exp2


let rec check_cmd locs = function
  | Syntax.Assign (l, exp) ->
      if check_exp locs exp then Some (l :: locs) else None
  | Syntax.IfThenElse (bexp, cmd1, cmd2) ->
      if check_bexp locs bexp
      then
        match (check_cmd locs cmd1, check_cmd locs cmd2) with
        | None, _ ->
            None
        | _, None ->
            None
        | Some locs1, Some locs2 ->
            Some (List.filter (fun loc -> List.mem loc locs2) locs1)
      else None
  | Syntax.Seq (c1, c2) -> (
    match check_cmd locs c1 with
    | None ->
        None
    | Some locs' ->
        check_cmd locs' c2 )
  | Syntax.Skip ->
      Some locs
  | Syntax.WhileDo (bexp, cmd) ->
      if check_bexp locs bexp then check_cmd locs cmd else None


let check cmd = match check_cmd [] cmd with None -> false | Some _ -> true
