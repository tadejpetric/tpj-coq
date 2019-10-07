let pi = 4.0 *. atan 1.0

let pozdravi = function
  | "Matija" -> "Dober dan, gospod predavatelj!"
  | "Žiga" -> "Oj!"
  | "" -> ""
  | "*" -> "Živjo, zvezdica!"
  | "**" -> "Živjo, zvezdici!"
  | "***" -> "Živjo, zvezdice!"
  | _ -> "Živjo, kdorkoli že si!"

let rec fakulteta = function
  | 0 -> 1
  | n -> n * fakulteta (n - 1)