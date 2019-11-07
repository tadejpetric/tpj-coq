## Naloga 1

Zapišite evaluacijsko drevo za naslednja ukaza v jeziku IMP:

  1. `#a := 1; if #a < 2 then #b := 2 * #a else #b := 0`
  
  2. `#a := 0; while #a < 2 do #a := #a + 1` 

## Naloga 2

Dopolnite operacijsko semantiko jezika IMP z:

  1. Logičnima operacijama `&&` in `||`. Primerjajte pravila kjer izračunamo vrednosti obeh argumentov in t.i. 'short-circuit evaluation', ki vrednost drugega argumenta izračuna zgolj če je to potrebno.

  2. Operacijo CAS (compare and swap), kjer `cas loc n m` preveri, ali ima lokacija `loc` vrednost `n`. V primeru ujemanja vrednost lokacije posodobi na `m`, sicer ne spremeni ničesar.


## Naloga 3

Zapišite induktivno definicijo seznamov z elementi iz množice A in nato izpeljite pravila za dokaz z indukcijo.

V nadaljevanju bomo uporabljali OCaml notacijo za sezname, torej `[]` in `x :: xs` za konstruktorja in `l1 @ l2` za lepljenje seznamov.

Definirajte manjkajoče funkcije in z indukcijo pokažite enakosti:

  1. `xs @ [] = xs` 

  2. `reverse (xs @ ys) = reverse ys @ reverse xs`

  3. `reverse (reverse xs) = xs`

  4. `map f (map g xs) = map (fun x -> f (g x)) xs` 

  5. `map f (reverse xs) = reverse (map f xs)`

## Naloga 4

Pokažite, da lahko podmnožico naraščajočih seznamov podamo z induktivno relacijo.

## Naloga 5

Zapišite induktivno definicijo dvojiških dreves z vrednostmi iz množice A in nato izpeljite pravila za dokaz z indukcijo.

Za funkciji
```
let rec mirror = function
  | Empty -> Empty
  | Node (lt, x, rt) -> Node (mirror rt, x, mirror lt)

let rec depth = function
  | Empty -> 0
  | Node (lt, x, rt) -> max (depth lt) (depth rt)
```
pokažite `depth tree = depth (mirror tree)`. Katero lastnost funkcije `max` je  potrebno privzeti?


Nato napišite funkciji `tree_map` in `tree_to_list` in dokažite enakost

``` tree_to_list (tree_map f tree) = list_map f (tree_to_list tree) ```

## Naloga 6

Razširite izrek o varnosti za jezik IMP za konstrukciji iz Naloge 1.