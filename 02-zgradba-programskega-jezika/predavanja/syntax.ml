type location = Location of string

type exp =
  | Lookup of location
  | Int of int
  | Plus of exp * exp
  | Minus of exp * exp
  | Times of exp * exp

type bexp =
  | Bool of bool
  | Equal of exp * exp
  | Less of exp * exp
  | Greater of exp * exp

type cmd =
  | Assign of location * exp
  | IfThenElse of bexp * cmd * cmd
  | Seq of cmd * cmd
  | Skip
  | WhileDo of bexp * cmd
