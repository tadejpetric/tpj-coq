let rec stakni xs ys =
    match xs with
    | [] -> ys
    | x :: xs' -> x :: stakni xs' ys

let rec (@@) xs ys =
    match xs with
    | [] -> ys
    | x :: xs' -> x :: xs' @@ ys

let rec map f = function
    | [] -> []
    | x :: xs -> f x :: map f xs

type 'a seznam =
  | Prazen
  | Sestavljen of 'a * 'a seznam

let rec stakni xs ys =
    match xs with
    | Prazen -> ys
    | Sestavljen (glava, rep) -> Sestavljen (glava, stakni rep ys)
