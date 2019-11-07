type 'value result = Ok of 'value * char list | Error of string

type 'value parser = {run: char list -> 'value result}

let explode str = List.init (String.length str) (String.get str)

let implode chrs = String.init (List.length chrs) (List.nth chrs)

let error msg = {run= (fun _ -> Error msg)}

let ok v = {run= (fun chrs -> Ok (v, chrs))}

let bind parser1 parser2 =
  { run=
      (fun chrs ->
        match parser1.run chrs with
        | Ok (v, chrs') -> (parser2 v).run chrs'
        | Error msg -> Error msg ) }

let or_else parser1 parser2 =
  { run=
      (fun chrs ->
        match parser1.run chrs with
        | Ok (res, chrs') -> Ok (res, chrs')
        | Error msg -> parser2.run chrs ) }

let map f p =
  { run=
      (fun chrs ->
        match p.run chrs with
        | Ok (v, chrs') -> Ok (f v, chrs')
        | Error msg -> Error msg ) }

let fix parserDef =
  let rec lazyParser = lazy (parserDef parser)
  and parser = { run = fun chrs -> (Lazy.force lazyParser).run chrs }
  in
  parser

let fix2 parserDef1 parserDef2 =
  let rec lazyParser1 = lazy (parserDef1 parser1 parser2)
  and lazyParser2 = lazy (parserDef2 parser1 parser2)
  and parser1 = { run = fun chrs -> (Lazy.force lazyParser1).run chrs }
  and parser2 = { run = fun chrs -> (Lazy.force lazyParser2).run chrs }
  in
  parser1, parser2
      
let (++) parser1 parser2 = bind parser1 (fun e1 -> map (fun e2 -> (e1, e2)) parser2)
let (+-) parser1 parser2 = bind parser1 (fun e1 -> map (fun _ -> e1) parser2)
let (-+) parser1 parser2 = bind parser1 (fun _ -> parser2)
let (--) parser1 parser2 = bind parser1 (fun _ -> map (fun _ -> ()) parser2)

let eof =
  {run= (function [] -> Ok ((), []) | _ -> Error "Characters remaining")}

let character chr =
  { run=
      (fun chrs ->
        match chrs with
        | chr' :: chrs' when chr = chr' -> Ok (chr, chrs')
        | _ -> Error "Expected character" ) }

let one_of parsers = List.fold_right or_else parsers (error "All parsers failed")

let digit =
  ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9']
  |> List.map character |> one_of

let many parser = fix (fun many ->
  one_of [
    parser ++ many |> map (fun (v, vs) -> v :: vs);
    ok []
    ]
)

let many1 parser =
    parser ++ many parser |> map (fun (v, vs) -> v :: vs)

let integer =
  many1 digit
  |> map implode
  |> map int_of_string

let option parser =
  or_else (map (fun v -> Some v) parser) (ok None)

let parens parser =
  character '(' -+ parser +- character ')'

type expr = Int of int | Plus of expr * expr | Times of expr * expr

let expr, _ = fix2 (fun expr atomic_expr ->
  one_of [
    atomic_expr +- character '+' ++ atomic_expr |> map (fun (e1, e2) -> Plus (e1, e2));
    atomic_expr +- character '*' ++ atomic_expr |> map (fun (e1, e2) -> Times (e1, e2));
    atomic_expr;
  ]
) (fun expr atomic_expr ->
  one_of [
    integer |> map (fun n -> Int n);
    parens expr;
  ]
)

let b = (expr +- eof).run (explode "(1+3)*(2+3)")