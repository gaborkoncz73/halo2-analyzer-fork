# Már Levezetett Lefedés Újrahasználata

A következő általános javítás a [teljes modellminták megosztása](shared-model-samples.md).
Az alábbi mérés a lefedés-újrahasználati v7 szabályzat eredményét rögzíti;
a jelenlegi v8 futásadatai a hivatkozott dokumentumban szerepelnek.

A recovery refinementje az aktuális Delta lefedő domainjéből indul. Ha a
következtetési szabályok vagy egy korábbi SMT-lépés már levezette, hogy minden
megvalósítható érték D-ben van, a rendszer nem kér újra SMT-bizonyítékot erre.
Ez a nem teljes domainekre is érvényes: a lefedés és az összes jelölt
megvalósíthatósága külön tulajdonság.

## Működés

1. Az aktuális, valódi recovery-állapotból veszi át D-t, nem a modellmintákból
   vagy egy hipotetikus szimulációból.
2. Csak a D-beli jelölteket vizsgálja `Gamma AND v=c` kérdésekkel, a többi cella
   már levezetett pontos értékeinek és kis domainjeinek újrahasználatával.
3. A korábban bizonyított SAT-jelölteket és kizárásokat nem ellenőrzi újra.
   A jelölt rögzítése már önmagában biztosítja, hogy a keresés D-n belül marad.
4. UNSAT esetén kizárhatja a jelöltet; SAT esetén megőrzi a megvalósítható mintát;
   timeout vagy el nem végzett vizsgálat esetén megtartja a lehetőséget.
5. A többértékű domain csak akkor teljes, ha minden megmaradt jelöltje
   bizonyítottan megvalósítható. A lefedés elfogadása önmagában nem állít teljességet.

A `DomainRefinementState` kizárólag az átadott `UcpResult.value_facts` domainjét
használja. A `RefinementCoverage::Established` belső jelölés rögzíti ezt a
szerződést. Tetszőleges, nem igazolt jelölthalmazt nem szabad ilyen állapotként
átadni. A hamis domain kimutatása a külön, eredeti kontextusból dolgozó
validálás feladata; ez továbbra sem feltételezi a recovery eredményeit.
Az önálló ellenőrző tesztsegéd megtartja az eredeti lefedési kérdést ismeretlen
eredetű jelölthalmazok vizsgálatához. Ez nem a recovery normál futási útvonala.

## Keretek És Ütemezés

Egy N elemű domain teljes vizsgálata legfeljebb N új jelöltkérdést igényel,
nem N+1-et. Az előzetes lefedési hívás nem szerepel a költségbecslésben,
a köztes cellák engedélyezési küszöbében vagy a solverhívások számában.
A premisszafeloldó kizárás után már egyetlen hívással visszatérhet az UCP-hez.
A kumulatív keretek, a változatlan állapotú újrapróbálkozás tiltása és a
SAT-minták újrahasználata változatlanok. A szabályzatok:
`established-domain-refine-discover-v7` és `established-domain-refinement-v7`.

## Díjkatalógusos Invoice

Azonos release build, `refinement` profil, 3000 ms/hívás és 48 hívásos keret
mellett az új egyszeri futás:

| Mutató | Lefedés-újraellenőrzéssel, korábbi v6 | Meglévő lefedés újrahasználatával |
| --- | ---: | ---: |
| Teljes API-idő | 88,92 s | 92,42 s |
| Solverhívások | 48 | 48 |
| Pontos célértékek | 7 | 7 |
| Többértékű cél-domainek | 14 | 14 |
| Teljes cél-domainek | 7 | 15 |
| Bizonyítottan nem egyedi célok | 1 | 10 |
| Ismeretlen egyértelműségű célok | 13 | 4 |

Mind a négy kosármennyiség kételemű domainje teljesnek és nem egyedinek
igazolódott. Ugyanez teljesült a termékösszeg, kedvezmény, adóalap és adó
kételemű halmazaira. A futás továbbra is részleges, `QueryLimitReached` állapotú;
egyes jelöltvizsgálatok timeoutoltak. A teljes idő nem csökkent, mert ugyanazt
a híváskeretet több érdemi jelöltellenőrzésre használta fel. Ezek egyszeri
futások, nem ismételt benchmarkok vagy általános gyorsulási garanciák.

## További Ellenőrzés

Azonos release buildben az alap invoice 0,81 s alatt, 14 hívással, a H=21
jóváhagyásos változat 2,59 s alatt, 24 hívással végzett. Előbbinél mind a
19, utóbbinál mind a 21 cél-domain teljesnek igazolódott. A korábbi v6
hívásszám rendre 16 és 28 volt. A technikai settlement-példa 2,38 s,
23 hívás és 25 teljes domain eredményt adott, valódi UCP--SMT--UCP átadással.
Ezek szintén egyszeri, nem átlagolt mérések.

A teljes soros release könyvtári tesztkészlet 496 sikeres, 0 hibás és 13
szándékosan kihagyott teszttel zárult. A kihagyott alap invoice-, H=21- és
díjkatalógusos recovery-tesztek külön is sikeresek. Az all-targets fordítási
ellenőrzés, a módosított Rust-fájlok formázásellenőrzése és a diff
whitespace-ellenőrzése szintén sikeres.
