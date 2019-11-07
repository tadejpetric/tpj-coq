type expr =
  | Num of int
  | Plus of expr * expr
  | Minus of expr
  | Times of expr * expr

let rec eval = function
  | Num n -> n
  | Plus (e1, e2) -> eval e1 + eval e2
  | Minus e -> - (eval e)
  | Times (e1, e2) -> eval e1 * eval e2

type 'a parser = char list -> ('a * char list) option

let char_parser = function
  | [] -> None
  | chr :: chrs -> Some (chr, chrs)

let return v = function chrs -> Some (v, chrs)

let (||) parser1 parser2 = function chrs ->
    match parser1 chrs with
    | None -> parser2 chrs
    | Some (v, chrs') -> Some (v, chrs')

let satisfy parser pred = function chrs ->
    match parser chrs with
    | None -> None
    | Some (v, chrs') ->
        if pred v then Some (v, chrs') else None

let stevka = satisfy char_parser (fun chr -> String.contains "0123456789" chr)

let crka = satisfy char_parser (fun chr -> String.contains "abcdef" chr)

let znak_ali_vprasaj = char_parser || return '?'

let explode str = List.init (String.length str) (String.get str)

let stevka_ali_crka = stevka || crka

let (++) parser1 parser2 = function chrs ->
    match parser1 chrs with
    | None -> None
    | Some (v1, chrs') ->
        match parser2 chrs' with
        | None -> None
        | Some (v2, chrs'') -> Some ((v1, v2), chrs'')

let dve_stevki = stevka ++ stevka

let dve_stevki_ali_dve_crki = (stevka ++ stevka) || (crka ++ crka)
