type 'value parser = {run: char list -> ('value * char list) option}

let explode str = List.init (String.length str) (String.get str)

let implode chrs = String.init (List.length chrs) (List.nth chrs)

let parse parser str =
  match str |> String.trim |> explode |> parser.run with
  | Some (v, []) -> v
  | Some (_, remaining) ->
      let remaining_length = List.length remaining in
      let parsed_length = String.length str - remaining_length in
      let parsed = String.sub str 0 parsed_length in
      let remaining = String.sub str parsed_length remaining_length in
      print_endline (parsed ^ remaining);
      print_endline (String.make parsed_length ' ' ^ "^");
      failwith "Parsing error"
  | None -> failwith "Parsing error"

let fail = {run= (fun _ -> None)}

let return v = {run= (fun chrs -> Some (v, chrs))}

let bind parser1 parser2 =
  { run=
      (fun chrs ->
        match parser1.run chrs with
        | Some (v, chrs') -> (parser2 v).run chrs'
        | None -> None ) }

let (||) parser1 parser2 =
  { run=
      (fun chrs ->
        match parser1.run chrs with
        | Some (v, chrs') -> Some (v, chrs')
        | None -> parser2.run chrs ) }

let map f p =
  { run=
      (fun chrs ->
        match p.run chrs with
        | Some (v, chrs') -> Some (f v, chrs')
        | None -> None ) }

let (>>=) = bind
let (>>) parser1 parser2 = parser1 >>= (fun _ -> parser2)

let eof =
  {run= (function [] -> Some ((), []) | _ -> None)}

let character chr =
  { run=
      (fun chrs ->
        match chrs with
        | chr' :: chrs' when chr = chr' -> Some (chr, chrs')
        | _ -> None ) }

let one_of parsers = List.fold_right (||) parsers fail

let word str =
  explode str
  |> List.map character
  |> List.fold_left (>>) (return ' ') 
  |> map ignore

let digit =
  "0123456789"
  |> explode
  |> List.map character
  |> one_of

let rec many parser = { run = fun chrs ->
  (one_of [
    parser >>= (fun v -> many parser >>= fun vs -> return (v :: vs));
    return [];
  ]).run chrs }

let many1 parser =
    parser >>= (fun v -> many parser >>= fun vs -> return (v :: vs))

let integer =
  many1 digit
  |> map implode
  |> map int_of_string

let space = many (character ' ' || character '\n') |> map ignore
let space1 = many1 (character ' ' || character '\n') |> map ignore
let parens parser =
  character '(' >>
  space >>
  parser >>= fun p ->
  space >>
  character ')' >>
  return p

let location =
  (* #n *)
  character '#' >>
  integer >>= fun l ->
  return (Syntax.Location l)

let rec exp = { run = fun chrs ->
  let parser = one_of [
    (* e1 + e2 *)
    (
      atomic_exp >>= fun e1 ->
      space >>
      character '+' >>
      space >>
      atomic_exp >>= fun e2 ->
      return (Syntax.Plus (e1, e2))
    );
    (* e1 - e2 *)
    (
      atomic_exp >>= fun e1 ->
      space >>
      character '-' >>
      space >>
      atomic_exp >>= fun e2 ->
      return (Syntax.Minus (e1, e2))
    );
    (* e1 * e2 *)
    (
      atomic_exp >>= fun e1 ->
      space >>
      character '*' >>
      space >>
      atomic_exp >>= fun e2 ->
      return (Syntax.Times (e1, e2))
    );
    atomic_exp
  ]
  in parser.run chrs }
and atomic_exp = { run = fun chrs ->
  let parser = one_of [
    (* l *)
    (
      location >>=
      fun l -> return (Syntax.Lookup l)
    );
    (* n *)
    (
      integer >>= fun n ->
      return (Syntax.Int n)
    );
    (* (e) *)
    parens exp;
  ] in parser.run chrs }

let bexp =
  one_of [
    (* true *)
    (
      word "true" >>
      return (Syntax.Bool true)
    );
    (* false *)
    (
      word "false" >>
      return (Syntax.Bool false)
    );
    (* e1 = e2 *)
    (
      exp >>= fun e1 ->
      space >> character '=' >> space >>
      exp >>= fun e2 ->
      return (Syntax.Equal (e1, e2))
    );
    (* e1 < e2 *)
    (
      exp >>= fun e1 ->
      space >> character '<' >> space >>
      exp >>= fun e2 ->
      return (Syntax.Less (e1, e2))
    );
    (* e1 > e2 *)
    (
      exp >>= fun e1 ->
      space >> character '>' >> space >>
      exp >>= fun e2 ->
      return (Syntax.Greater (e1, e2))
    )
  ]

let rec cmd = {run = fun chrs ->
  let parser = one_of [
    (* if b then c1 else c2 *)
    (
      word "if" >> space1 >>
      bexp >>= fun b ->
      space1 >> word "then" >> space1 >>
      cmd >>= fun c1 ->
      space1 >> word "else" >> space1 >>
      cmd >>= fun c2 ->
      return (Syntax.IfThenElse (b, c1, c2))
    );
    (* while b do c *)
    (
      word "while" >> space1 >>
      bexp >>= fun b ->
      space1 >> word "do" >> space1 >>
      cmd >>= fun c ->
      return (Syntax.WhileDo (b, c))
    );
    (* c1; c2 *)
    (
      atomic_cmd >>= fun c1 ->
      space >> character ';' >> space >>
      cmd >>= fun c2 ->
      return (Syntax.Seq (c1, c2))
    );
    atomic_cmd
  ]
  in parser.run chrs }
and atomic_cmd = {run = fun chrs ->
  let parser = one_of [
    (* l := e *)
    begin
      location >>= fun l ->
      space >> word ":=" >> space >>
      exp >>= fun e ->
      return (Syntax.Assign (l, e))
    end;
    (* skip *)
    begin
      word "skip" >>
      return Syntax.Skip
    end;
    parens cmd;      
  ]
  in parser.run chrs }
