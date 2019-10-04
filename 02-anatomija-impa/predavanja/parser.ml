type 'value result = Ok of 'value * char list | Error of string

type 'value parser = {run: char list -> 'value result}

let explode str = List.init (String.length str) (String.get str)

let implode chrs = String.init (List.length chrs) (List.nth chrs)

let parse parser str =
  match parser.run (explode str) with
  | Ok (v, []) -> v
  | Ok (_, remaining) ->
      let remaining_length = List.length remaining in
      let parsed_length = String.length str - remaining_length in
      let parsed = String.sub str 0 parsed_length in
      let remaining = String.sub str parsed_length remaining_length in
      print_endline (parsed ^ remaining);
      print_endline (String.make parsed_length ' ' ^ "^");
      failwith "Parsing error"
  | Error msg -> failwith ("Parsing error: " ^ msg)

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

let sequence parsers =
  List.fold_right (fun parser1 parser2 -> bind parser1 (fun v -> map (fun vs -> v :: vs) parser2)) parsers (ok [])

let word str =
  explode str
  |> List.map character
  |> sequence
  |> map implode

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

type location = Location of int
type exp = Lookup of location | Int of int | Plus of exp * exp |  Minus of exp * exp | Times of exp * exp
type bexp = Bool of bool | Equal of exp * exp
type cmd =
  | Assign of location * exp
  | IfThenElse of bexp * cmd * cmd
  | Seq of cmd * cmd
  | Skip
  | WhileDo of bexp * cmd

let space = many (character ' ') |> map ignore
let space1 = many1 (character ' ') |> map ignore
let spaced parser = space -+ parser +- space

let location = character '#' -+ integer |> map (fun l -> Location l)

let exp, _ = fix2 (fun exp atomic_exp ->
  one_of [
    atomic_exp +- character '+' ++ atomic_exp |> map (fun (e1, e2) -> Plus (e1, e2));
    atomic_exp +- character '-' ++ atomic_exp |> map (fun (e1, e2) -> Minus (e1, e2));
    atomic_exp +- character '*' ++ atomic_exp |> map (fun (e1, e2) -> Times (e1, e2));
    atomic_exp;
  ] |> spaced
) (fun exp atomic_exp ->
  one_of [
    location |> map (fun l -> Lookup l);
    integer |> map (fun n -> Int n);
    parens exp;
  ] |> spaced
)

let bexp =
  one_of [
    word "true" |> map (fun _ -> Bool true);
    word "false" |> map (fun _ -> Bool false);
    exp +- character '=' ++ exp |> map (fun (e1, e2) -> Equal (e1, e2));
  ] |> spaced

let cmd, atomic_cmd = fix2 (fun cmd atomic_cmd ->
  one_of [
    word "if" -- space -+ bexp +- space +- word "then" +- space ++ cmd +- space +- word "else" +- space ++ cmd |> map (fun ((b, c1), c2) -> IfThenElse (b, c1, c2));
    word "while" -- space -+ bexp +- space +- word "do" +- space ++ cmd |> map (fun (b, c) -> WhileDo (b, c));
    atomic_cmd +- character ';' ++ cmd |> map (fun (c1, c2) -> Seq (c1, c2));
    atomic_cmd
  ] |> spaced
) (fun cmd atomic_cmd ->
  one_of [
    location +- space +- word ":=" ++ exp |> map (fun (l, e) -> Assign (l, e));
    word "skip" |> map (fun _ -> Skip);
    parens cmd;      
  ] |> spaced
)

let b = parse cmd "while #2 = 3 do #2 := 10"