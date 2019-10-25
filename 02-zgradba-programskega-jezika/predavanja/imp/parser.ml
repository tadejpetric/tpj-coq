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
  let is_alpha = String.contains "abcdefghijklmnopqrstvwuxyz" in
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
  many (alpha || digit) >>= fun chrs ->
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

let binop parser op f =
  parser >>= fun v1 ->
  spaces >>
  word op >>
  spaces >>
  parser >>= fun v2 ->
  return (f v1 v2)

(* IMP PARSERS *)

let location =
  word "#" >>
  ident >>= fun ident ->
  return (Syntax.Location ident)


let rec exp chrs =
  one_of
    [ binop atomic_exp "+" (fun e1 e2 -> Syntax.Plus (e1, e2))
    ; binop atomic_exp "-" (fun e1 e2 -> Syntax.Minus (e1, e2))
    ; binop atomic_exp "*" (fun e1 e2 -> Syntax.Times (e1, e2))
    ; atomic_exp ]
    chrs


and atomic_exp chrs =
  one_of
    [ (location >>= fun l -> return (Syntax.Lookup l))
    ; (integer >>= fun n -> return (Syntax.Int n))
    ; parens exp ]
    chrs


let bexp =
  one_of
    [ word "true" >> return (Syntax.Bool true)
    ; word "false" >> return (Syntax.Bool false)
    ; binop exp "=" (fun e1 e2 -> Syntax.Equal (e1, e2))
    ; binop exp "<" (fun e1 e2 -> Syntax.Less (e1, e2))
    ; binop exp ">" (fun e1 e2 -> Syntax.Greater (e1, e2)) ]


let rec cmd chrs =
  let if_then_else =
    word "if" >>
    spaces1 >>
    bexp >>= fun b ->
    spaces1 >>
    word "then" >>
    spaces1 >>
    cmd >>= fun c1 ->
    spaces1 >>
    word "else" >>
    spaces1 >>
    cmd >>= fun c2 ->
    return (Syntax.IfThenElse (b, c1, c2))
  and while_do =
    word "while" >>
    spaces1 >>
    bexp >>= fun b ->
    spaces1 >>
    word "do" >>
    spaces1 >>
    cmd >>= fun c ->
    return (Syntax.WhileDo (b, c))
  and seq =
    atomic_cmd >>= fun c1 ->
    spaces >>
    word ";" >>
    spaces >>
    cmd >>= fun c2 ->
    return (Syntax.Seq (c1, c2))
  in
  one_of [if_then_else; while_do; seq; atomic_cmd] chrs


and atomic_cmd chrs =
  let assign =
    location >>= fun l ->
    spaces >>
    word ":=" >>
    spaces >>
    exp >>= fun e ->
    return (Syntax.Assign (l, e))
  and skip =
    word "skip" >>
    return Syntax.Skip
  in
  one_of [assign; skip; parens cmd] chrs


let parse str =
  match str |> String.trim |> explode |> cmd with
  | Some (v, []) -> v
  | Some (_, _ :: _) | None -> failwith "Parsing error"
