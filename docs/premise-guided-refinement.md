# Premisszavezérelt Domainszűkítés

A változás az SMT-munka kiválasztását és az UCP-nek történő átadás időpontját
módosítja. Nem ad új matematikai következtetési szabályt, nem írja át a circuitet,
és nem emeli meg a solverkereteket.

## Általános Működés

Egy `a * (c*v+d) = 0` szorzatkényszernél a második tényező lehetséges nullahelye
akadályozhatja `a=0` levezetését. A tervező a meglévő, testaritmetikát használó
kifejezésdomain-visszavetítéssel keresi a tényezők affin nullahelyeit.
Csak olyan jelöltet vesz figyelembe, amely a vizsgált cella jelenlegi domainjében
szerepel. A konkrét szám, cellanév és sorszám nem része a heurisztikának.

Ezek a kritikus jelöltek kerülnek előre a legfeljebb négy kizárási szimulációban.
Ha egy jelölt hipotetikus kizárása más kijelölt célon pontos értéket vagy szűkebb
domaint eredményez, a tervező ezt ígéretes premisszafeloldásnak tekinti.
Egy önmagában álló logikai cella feltételezett pontossá válása nem kap ilyen
elsőbbséget; ehhez másik célra gyakorolt hatás szükséges.

A teljes vizsgálat keretbe férésének ellenőrzése és a 32 cellás pontozási korlát
megmarad. Ígéretes, keretbe férő kritikus vizsgálatnál nem pontozza végig az összes
általános alternatívát. Ha nincs ilyen lehetőség, a korábbi általános heurisztika
működik tovább. A haszon és a tervezett jelöltsorrend a meglévő állapotfüggő
gyorsítótárba kerül. A közös műveletválasztó ezt az eredményt új szimuláció nélkül
is felhasználja, és nem cseréli le pusztán egyértelműséget feltételező gyorspróbára.

## Korábbi Átadás

A tervezett jelöltet az SMT ténylegesen ellenőrzi. Csak az igazolt UNSAT válasz
után kerülhet ki a domainből. Ha a tervezés ettől propagációs előrelépést vár,
a szűkítés azonnal visszaadhatja a megmaradt lefedő domaint:

```text
lefedés ellenőrzése
kritikus jelölt ellenőrzése
UNSAT -> részlegesen szűkített domain -> UCP
új tudás -> a félbehagyott vizsgálat folytatása
```

A szándékos átadás `Partial` státuszú, önmagában nem timeout vagy keretkimerülés.
Az új tudásgeneráció után ezt a félbehagyott vizsgálatot egyszer előbb folytatja,
mint a még el nem kezdett általános szűkítéseket. Ez elkerülheti a más cellákon
közben elvégzett, majd további előrelépés után megismételt timeoutos próbákat.
Az egyéb újrapróbálkozások frissességi és régebbieket előresoroló szabályai megmaradnak.

A folytatás nem ismétli meg a már bizonyított SAT/UNSAT jelöltellenőrzéseket.
A lefedést csak akkor használja újra, ha a korábbi lefedés és az igazolt kizárások
elegendők a jelenlegi domainhez. A globális solverkeret nem nullázódik.
Változatlan K/Delta mellett nincs újabb kísérlet; újabb korai átadáshoz új
igazolt kizárás kell. A hipotetikus szimulációkból semmi sem kerül K-ba, Deltába
vagy a megvalósítható minták közé. UNKNOWN vagy SAT nem jogosít kizárásra.

## Számlapélda Mérése

A circuit, a publikus értékek és a keretek változatlanok: 3000 ms solverhívásonként,
48 szűkítési hívás és ugyanaz a 21 kijelölt cél. A kezdeti SAT-ot ellenőrzött
tanú igazolja, a privát tanúértékek nem elemzési premisszák.

| Rész | Közvetlenül előtte mért régi ütemező | Új ütemező |
| --- | ---: | ---: |
| Első UCP | 10,08 s | 9,08 s |
| Első SMT | 33,17 s / 22 hívás | 0,03 s / 2 hívás |
| Második UCP | 4,37 s | 3,95 s |
| Összes solverhívás | 27 | 14 |
| Teljes idő | 69,56 s | 27,66 s |
| Végső célok | 17 pontos, 4 többértékű domain | 17 pontos, 4 többértékű domain |

A régi ütemező a kedvezményt és kupont vizsgálta először, majd a jóváhagyási mód
teljes szűkítését próbálta végigvinni az új UCP előtt. Az új ütemező elsőként
csak az 5-öt zárja ki. A kilencelemű lefedő domain már elég a felár és a kosár
visszaállításához. A mód további kilenc ellenőrzése ezután 0,22 s alatt lezárult,
teljes `{3,7}` domainnel. A domain változása egy harmadik, új célérték nélküli
UCP-fázist is elindított. Végül három lefedésellenőrzés összesen 9,01 s alatt
timeoutolt. Az egyéb előkészítés és ütemezés 12,79 s-ról 5,37 s-ra csökkent.

Ezek egyszeri futások, nem átlagok vagy univerzális gyorsulási garanciák.
A gyorspróbákat is engedő `combined` profil új futása 26,30 s és 19 hívás lett;
ebben mind a négy többértékű cél nemegyértelműségét igazolta, és a kupon
domainje is teljesnek tanúsított lett. A beszállítói domainek lefedésellenőrzései
ebben a profilban is timeoutoltak.

A teljes parancsok és a független referencia az
[összefüggő számlapélda leírásában](invoice-approval-demo.md) találhatók.

## Hatókör És Ellenőrzés

- A kritikus gyökök felismerése a meglévő szorzatalakra és affin visszavetítésre épül;
  nem általános polinomfaktorizáló. Egyenletenként legfeljebb 64 tényezőt vizsgál.
- A heurisztika nem becsül SAT-valószínűséget, és nem tanul solverfutásidő-modellt.
  A gyorsítás a jobb kérdéssorrendből, korábbi átadásból és kisebb pontozási munkából ered.
- A regressziók több eltérő kritikus értéket, átnevezett és eltolt cellákat,
  testbeli aliasokat, SAT/UNKNOWN megőrzést, korlátos folytatást, a gyorsítótár
  használatát és a hipotetikus tények különválasztását ellenőrzik.
- A tesztek nem helyettesítik a formális helyességi bizonyítást. A kizárás,
  lefedés és megvalósíthatóság bizonyítási premisszái változatlanok.

A végső soros könyvtári regresszió 492 sikeres, 0 hibás és 11 szándékosan
kihagyott teszttel zárult, 156,89 s alatt. A két teljes számlaprofil külön is
lefutott. A settlement-visszacsatolási kontroll 26 solverhívással, 22 pontos
értékkel és három teljes többértékű domainnel zárult 5,31 s alatt; a korábbi
bitet először vizsgáló változat 29 hívást használt. Az összes target fordítási
ellenőrzése, az érintett Rust-fájlok formázása és a diff whitespace-ellenőrzése is sikeres.

A mérési metaadatok új szabályzatnevei:
`premise-guided-resumable-domain-refinement-v4` és
`premise-guided-refine-discover-v5`.
