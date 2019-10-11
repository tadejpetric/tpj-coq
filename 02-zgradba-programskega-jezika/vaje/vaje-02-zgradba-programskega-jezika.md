## Naloga 1
Napišite sintaktično drevo, ki ustreza programom:

```
#a := 2 + #b
```

```
if #x = 2 then 
  #x := 3
else
  skip
```

```
while #z > 0 do 
  #z := #z - 1;
  #w := #z + #w
```

```
(while #z > 0 do #z := #z - 1);
#w := #z + #w
```

## Naloga 2
Programe najprej napišite v OCamlu, nato pa jih prevedite v programski jezik IMP s predavanj.

1. Napišite program, ki sešteje vsa naravna števila manjša od `n`.

2. Napišite program, ki preveri ali je podano število praštevilo.

## Naloga 3
Razmislite, kako bi dopolnili sintakso in evaluator jezika IMP za:

1. logična veznika `&&` in `||`,

2. ukaz `switch`, ki zamenja vrednosti dveh lokacij,

3. ukaz `fail`, ki prekine izvajanje programa.

## Naloga 4
Izboljšajte parser, da bo dopolnil nepopolne `if` stavke. Ukaz `if b then c` naj se prevede v enako sintaktično drevo kot `if b then c else skip`.

## Naloga 5
Dopolnite vse dele IMPa s podporo za `for` zanke oblike:
```
for #x := 0 to 100 do
  cmd
```
Pri tem sta `0` in `100` seveda zgolj zgled poljubnih aritmetičnih izrazov.