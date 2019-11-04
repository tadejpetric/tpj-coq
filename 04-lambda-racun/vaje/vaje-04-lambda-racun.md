## Naloga 1

S semantiko velikih korakov izračunajte:

1. `2 + 2 > 3`
2. `(fun x -> x * x) 5`
3. `(fun x -> (fun y -> x = y)) 2 3`

S semantiko malih korakov izračunajte zaporedje korakov, ki izračunajo vrednost izrazov:

1. `(2 * 2) + (3 * 3)` 
2. `(fun x -> if x + 1 > 0 then x else 0) 12`


## Naloga 2

Pristop *call-by-value* oz. *neučakano izvajanje* pri uporabi funkcije najprej izračuna vrednost argumenta in dobljeno vrednost substituira v telo funkcije. Pri pristopu *call-by-name* oz. *lenem izvajanju* pa pri uporabi funkcije argument še neizračunan substituiramo v telo funkcije.

Popravite semantiko velikih in malih korakov iz *CBV* na *CBN* (v trenutnem lambda računu je potrebno spremeniti zgolj funkcije).

Primerjajte delovanje *CBV* in *CBN* na primerih:

1. `(fun x -> (fun y -> if x > 0 then y else 0)) 1 (4*((4+2)*3))`
2. `(fun x -> (x * x) + x) (3*(2+(4*0)))`

## Naloga 3

Razširite lambda račun s pari, seznami in vsotami. Za pare dodajte projekciji na posamezno komponento, za sezname in vsote pa dodajte razgrajevalnik `match`.

Kot dodaten izziv premislite, kako razširitve narediti v pristopu *CBN* in napišite funkcijo, ki zgradi neskončen seznam ničel.