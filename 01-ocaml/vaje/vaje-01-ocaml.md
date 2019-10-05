## Naloga 1
Sledeče funkcije napišite v OCaml sintaksi in vsaki izmed njih priredite smiseln tip.

1. Funkcija `cube_minus_square` izračuna razliko med kvadratom in kubom podanega števila.

2. Funkcija `init_list` sprejme element `x` in celo število `n` ter zgradi seznam `n` elementov `x`.

3. Funkcija `apply_100_times` sprejme funkcijo `f` in element `x`, ter `f` 100krat zaporedoma uporabi na `x`. Izračuna torej `f (f ... (f (f x)) ...)`.

## Naloga 2
V OCamlu napišite funkcijo `while_loop`, ki sprejme `cond`, `f` in `x` ter se obnaša kot zanka:
```
while cond(x):
  x = f(x)
return x
```
Kaj je tip funkcije `while_loop`?

Kako bi problem rešili za zanko:
```
result = 0
for x in list:
  result += f(x)
return result
```

## Naloga 3
Definirajte tip seznama celih števil s konstruktorjema `Cons n` in `Nil`. Nato definirajte funkcije:

1. `length`, ki vrne dolžino seznama,
2. `member`, ki za podan element preveri ali se nahaja v seznamu,
3. `map`, ki zgradi nov seznam kjer vse elemente seznama preslika s podano funkcijo.

## Naloga 4
Definirajte tip dvojiškega drevesa, ki v listih hrani cela števila. Nato napišite funkcijo `collect`, ki sešteje vse vrednosti v listih drevesa.

Kako bi problem posplošili na drevesa, ki v listih hranijo elemente tipa `'a` in katerih elemente združujemo z `combine acc x`, kjer `acc` predstavlja že pobrane elemente, `x` pa element v trenutnem listu.