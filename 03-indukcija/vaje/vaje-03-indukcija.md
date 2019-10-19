## Naloga 1

Dopolnite operacijsko semantiko jezika IMP z:

  1. Logičnima operacijama `&&` in `||`. Primerjajte pravila kjer izračunamo vrednosti obeh argumentov in t.i. 'short-circuit evaluation', ki vrednost drugega argumenta izračuna zgolj če je to potrebno.

  2. Operacijo CAS (compare and swap), kjer `cas loc n m` preveri, ali ima lokacija `loc` vrednost `n`. V primeru ujemanja vrednost lokacije posodobi na `m`, sicer ne spremeni ničesar.

  3. For zanko oblike `for l := n to m do c`.


## Naloga 2

Zapišite induktivno definicijo seznamov z elementi iz množice A in nato izpeljite pravila za dokaz z indukcijo.

V nadaljevanju bomo uporabljali OCaml notacijo za sezname, torej `[]` in `x :: xs` za konstruktorja in `l1 @ l2` za lepljenje seznamov.

Definirajte manjkajoče funkcije in z indukcijo pokažite enakosti:

  1. `xs @ [] = xs` 

  2. `reverse (xs @ ys) = revers ys @ reverse xs`

  3. `reverse (reverse xs) = xs`

  4. `map f (map g xs) = map (fun x -> f (g x)) xs` 

  5. `map f (reverse xs) = reverse (map f xs)`


## Naloga 3

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

## Naloga 4

Razširite izrek o varnosti za jezik IMP za konstrukcije iz Naloga 1.