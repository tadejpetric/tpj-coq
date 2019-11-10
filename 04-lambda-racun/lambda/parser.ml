let explode str = List.init (String.length str) (String.get str)

let implode chrs = String.init (List.length chrs) (List.nth chrs)

type 'value parser = char list -> ('value * char list) option

(* BASIC PARSERS *)

let fail _ = None

let return v chrs = Some (v, chrs)

let character = function
  | [] -> None
  | chr :: chrs -> Some (chr, chrs)


let ( || ) parser1 parser2 chrs =
  match parser1 chrs with
  | None -> parser2 chrs
  | Some (v, chrs') -> Some (v, chrs')


let ( >>= ) parser1 parser2 chrs =
  match parser1 chrs with
  | None -> None
  | Some (v, chrs') -> parser2 v chrs'

(* DERIVED PARSERS *)

let ( >> ) parser1 parser2 =
  parser1 >>= fun _ -> parser2

let satisfy cond parser =
  let cond_parser v =
    if cond v then return v else fail in
  parser >>= cond_parser

let digit =
  let is_digit = String.contains "0123456789" in
  character |> satisfy is_digit

let alpha =
  let is_alpha = String.contains "_abcdefghijklmnopqrstvwuxyz" in
  character |> satisfy is_alpha

let space =
  let is_space = String.contains " \n\t\r" in
  character |> satisfy is_space

let exactly chr = character |> satisfy (( = ) chr)

let one_of parsers = List.fold_right ( || ) parsers fail

let word str =
  let chrs = explode str in
  List.fold_right
    (fun chr parser -> exactly chr >> parser)
    chrs (return ())

let rec many parser = many1 parser || return []

and many1 parser =
  parser >>= fun v ->
  many parser >>= fun vs ->
  return (v :: vs)

let integer =
  many1 digit >>= fun digits ->
  return (int_of_string (implode digits))

let ident =
  alpha >>= fun chr ->
  many (alpha || digit || exactly '\'') >>= fun chrs ->
  return (implode (chr :: chrs))

let spaces = many space >> return ()

let spaces1 = many1 space >> return ()

let parens parser =
  word "(" >>
  spaces >>
  parser >>= fun p ->
  spaces >>
  word ")" >>
  return p

let binop parser1 op parser2 f =
  parser1 >>= fun v1 ->
  spaces >>
  word op >>
  spaces >>
  parser2 >>= fun v2 ->
  return (f v1 v2)

(* LAMBDA PARSERS *)

let rec exp3 chrs =
  let if_then_else =
    word "IF" >>
    spaces1 >>
    exp3 >>= fun e ->
    spaces1 >>
    word "THEN" >>
    spaces1 >>
    exp3 >>= fun e1 ->
    spaces1 >>
    word "ELSE" >>
    spaces1 >>
    exp3 >>= fun e2 ->
    return (Syntax.IfThenElse (e, e1, e2))
  and lambda =
    word "FUN" >>
    spaces1 >>
    ident >>= fun x ->
    spaces1 >>
    word "->" >>
    spaces1 >>
    exp3 >>= fun e ->
    return (Syntax.Lambda (x, e))
  and rec_lambda =
    word "REC" >>
    spaces1 >>
    ident >>= fun f ->
    spaces1 >>
    ident >>= fun x ->
    spaces1 >>
    word "->" >>
    spaces1 >>
    exp3 >>= fun e ->
    return (Syntax.RecLambda (f, x, e))
  and let_in =
    word "LET" >>
    spaces1 >>
    ident >>= fun x ->
    spaces >>
    word "=" >>
    spaces >>
    exp3 >>= fun e1 ->
    spaces1 >>
    word "IN" >>
    spaces1 >>
    exp3 >>= fun e2 ->
    return (Syntax.let_in (x, e1, e2))
  and let_rec_in =
    word "LET" >>
    spaces1 >>
    word "REC" >>
    spaces1 >>
    ident >>= fun f ->
    spaces >>
    ident >>= fun x ->
    spaces >>
    word "=" >>
    spaces >>
    exp3 >>= fun e1 ->
    spaces1 >>
    word "IN" >>
    spaces1 >>
    exp3 >>= fun e2 ->
    return (Syntax.let_rec_in (f, x, e1, e2))
  in
  one_of [if_then_else; lambda; rec_lambda; let_in; let_rec_in; exp2] chrs

and exp2 chrs =
  one_of
    [ binop exp1 "*" exp2 (fun e1 e2 -> Syntax.Times (e1, e2))
    ; binop exp1 "+" exp2 (fun e1 e2 -> Syntax.Plus (e1, e2))
    ; binop exp1 "-" exp2 (fun e1 e2 -> Syntax.Minus (e1, e2))
    ; binop exp1 "=" exp2 (fun e1 e2 -> Syntax.Equal (e1, e2))
    ; binop exp1 "<" exp2 (fun e1 e2 -> Syntax.Less (e1, e2))
    ; binop exp1 ">" exp2 (fun e1 e2 -> Syntax.Greater (e1, e2))
    ; exp1 ]
    chrs

and exp1 chrs =
  let apply =
    exp0 >>= fun e ->
    many1 (spaces1 >> exp0) >>= fun es ->
    return (List.fold_left (fun e1 e2 -> Syntax.Apply (e1, e2)) e es)
  in
  one_of
    [ apply
    ; exp0 ]
    chrs


and exp0 chrs =
  one_of
    [ (integer >>= fun n -> return (Syntax.Int n))
    ; word "TRUE" >> return (Syntax.Bool true)
    ; word "FALSE" >> return (Syntax.Bool false)
    ; (ident >>= fun x -> return (Syntax.Var x))
    ; parens exp3 ]
    chrs


let parse str =
  match str |> String.trim |> explode |> exp3 with
  | Some (v, []) -> v
  | Some (_, _ :: _) | None -> failwith "Parsing error"
