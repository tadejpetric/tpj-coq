## Naloga 1

Preverite tipe izrazov. Izrazi morda nimajo primernega tipa. V tem primeru poiščite mesto, kjer se postopek zatakne.

  1. `b:bool, x:int |- 1 + (if b then 2 else x) : int`
  2. `|- fun x -> (fun y -> x > y) : int -> int -> bool`
  3. `|- (rec f x -> if x then f x else 0) true : int`
  4. `f : int -> int |- (f 3) > (f (f 0)) 2 : bool`

## Naloga 2

Napišite nekaj izrazov, katerim ni možno dodeliti tipa, vendar se izračunajo v vrednost.

## Naloga 3

Razširite jezik in sistem tipov s pari, seznami in vsotami. Za pare dodajte projekciji na posamezno komponento, za sezname in vsote pa dodajte razgrajevalnik `match`.

## Naloga 4

V jeziku iz naloge 3 poiščite primeren tip za spodnji izraz in ustreznost preverite z izpeljavo. V primeru sta z `fst` in `snd` označeni projekciji na prvo in drugo komponento para.

``` (fun p -> (match fst p with [] -> true | x :: xs -> snd p)) (1::2::[], false) ```
