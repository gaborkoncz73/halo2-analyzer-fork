# UCP és keresési teljesítmény

Az alábbi cache-mérések a korábbi, még sikertelen visszaállítás történetét
rögzítik. Az új lineáris/intervallumos következtetés már **16 konkrét célértéket**
visszaállít ugyanazon circuitből. A végső teljes ellenőrzött futás **66,11 s,
8 SMT-hívás, `Analyzed`** eredményt adott; a végső újramérés és az általános
szabály leírása a [relációs következtetés dokumentációjában](ucp-relational-propagation.md)
és a [számlapélda útmutatójában](../korrekt/src/circuit_analyzer/ucp/thesis_examples/README.md)
található. A régi `0 exact / QueryLimitReached` eredmények nem a jelenlegi
következtetési képességet jellemzik.

## Jelenlegi Visszaállítás

| Mutató | Csak cache-gyorsítás után | Új lineáris/domain-következtetéssel |
| --- | ---: | ---: |
| Teljes kombinált futás | 236,08 s | 66,11 s |
| Tényleges SMT-hívás | 63 | 8 |
| Pontos célérték | 0 | 16 |
| Nem egyelemű lefedő cél-domain | 12 | 3 |
| Teljesnek tanúsított cél-domain | 0 | 17 |
| Riport | `QueryLimitReached` | `Analyzed` |

A jelenlegi önálló, solver nélküli UCP-futás **4,22 s** alatt ugyanazt a
16 pontos célértéket állította elő. A teljes kombinált futás nem azonos ezzel:
a publikus értékek nélküli szerkezeti alapállapotot is kiszámítja, majd a
fennmaradó három többértékű cél SMT-vizsgálatát is végzi. A profilban a két
normál UCP-futás együtt 59,69 s, a solverfolyamatok együtt 6,14 s időt adtak.
A szerkezeti alapállapot feltételes propagációja továbbra is jelentős költség.

A négy mennyiség `(37,29,25,33)`, a részösszeg `191600`. A kupon `{2,3}`, a
beszállítói vetületek `{4,10,16,22,28,34}` és `{3,9,15,21,27,33}` maradnak.
A független teljes referenciamodell az összes jelentett cél-domainnel egyezik,
de a riport csak a kupont tanúsítja teljesnek a három többértékű cél közül.
A két beszállítói domain továbbra is lefedő domainként szerepel, nem kap
teljességi jelölést pusztán a referencia ismerete miatt.

Ezek egyszeri fejlesztési futások, változatlan circuit és keresési keretek
mellett. A javulás nem általános solvergyorsulási garancia: erősebb UCP
szolgáltat több tényt a keresésnek. A teljes könyvtári regresszió **476 sikeres,
0 hibás és 10 szándékosan kihagyott teszt**, 173,47 s alatt. A külön bekapcsolt
teljes számlamérés és az összes target fordításellenőrzése is sikeres.

## Mérés

Az `ucp::profiling::ProfilingSession::start()` az aktuális szálon engedélyezi
a mérést. A `snapshot()` fázisonkénti hívásszámot és időt, valamint cache-számlálókat
ad vissza. A munkamenet végén visszaállítja a külső mérést; másik szál nem
használja ezeket a számlálókat. Profilozási munkamenet nélkül nem indít időmérést.

A fázisidők **befoglaló idők**, ezért összeadásuk hibás: például a
`ucp.propagation` tartalmazhat `ucp.conditional` futásokat, amelyek idejében a
`ucp.equation_domains` és `ucp.consistency` is benne van.
A `smt.process` a tényleges solverfolyamat felügyelt idejét méri, nem az összes
SMT-előkészítés és eredményfeldolgozás költségét.
A `ucp.propagation` hívásszáma a szerkezeti alapállapot számítását is tartalmazza;
a riport `propagation_runs` mezője csak a visszaállítási fázisokat számolja.
Ezért a tanúellenőrzéses számlamérésben a profil két normál futást, a riport
egy visszaállítási propagációt mutat, ellentmondás nélkül.

A számlapélda fixponttesztje és hosszú mérése automatikusan kiírja a profilt:

```bash
cargo test --offline -p korrekt --lib thesis_invoice_ucp -- --nocapture --test-threads=1
cargo test --offline -p korrekt --lib thesis_invoice_recovery_smoke -- --ignored --nocapture --test-threads=1
```

## Feltárt Ismétlések

A számlapélda első profilozott, debug UCP-futása 47,70 másodperc volt.
Ebben 256 feltételes vizsgálat összesen 47,36 másodpercet foglalt magába;
50 481 egyenlet-domainvizsgálat történt. Ezek nem függetlenül összeadandó idők.

A kifejezésszintű cache bevezetése után, még a további gyorsítások előtt,
ugyanaz a fixpont 15,76 másodperc alatt állt elő. A feltételes vizsgálatok száma
továbbra is 256, a kényszereké 79, az eredmény továbbra is 0 pontosan
visszaállított kiválasztott privát érték volt. A cache 92 120 találatot adott.
Ezek egyedi fejlesztési futások, nem átlagok és nem általános gyorsulási garanciák.

A végleges optimalizálásokkal végzett teljes, egyszeri kombinált mérés:

| Mutató | Eredmény |
| --- | ---: |
| Teljes idő | 236,08 s |
| Korábbi, optimalizálás előtti teljes idő | 560,53 s |
| Tényleges SMT-hívások | 63, változatlan |
| Solverfolyamatok ideje | 171,26 s |
| Refinement pontozási idő | 9,29 s |
| Refinement haszon-cache találat / hiány | 673 / 44 |
| Tényleges heurisztikai UCP-szimulációk | 635 |
| Visszaállítási UCP-fázisok | 1 |
| Pontos célérték / nem egyelemű covering domain | 0 / 12 |
| Végállapot | `QueryLimitReached` |

Ez a két fejlesztési futás körülbelül 2,37-szeres teljes időbeli különbséget mutat,
azonos beállításokkal és azonos erősségű eredménnyel. Nem ismételt statisztikai
sebességmérés. A kezdeti SAT-ot mindkét esetben a tényleges tanú ellenőrzése
igazolta; a keresési limitek és a circuit nem változtak. A solveroldali
időkorlátok továbbra is megakadályozzák a példa konkrét visszaállítását.

## Általános Gyorsítások

- A `propagation_cache.rs` kifejezésenként az utolsó bemeneti állapotot tárolja.
  Csak a hivatkozott cellák **azonos** domainje és teljességi jelölése mellett
  használja újra az érték/domain-következtetést vagy a kifejezésdomain értékelését.
  Az AST és a modulus a futáson belül változatlan. A normál futás és a feltételes
  ágak ugyanazt a cache-t használják, de eltérő feltételezés nem kaphat találatot.
- A `privacy_domain.rs` a refinement pontozásának kiszámított hasznát tárolja.
  Az aktuális probléma, teljes K/Delta-állapot és céllista strukturális egyezését
  ellenőrzi; a teljességi metaadat változása is érvénytelenít. A megmaradt solverkeret
  nem kerül a tárolt haszonba: a költséget és a keretbe férő munkát minden választásnál
  frissen értékeli. A célcellák és a köztes cellák eltérő céllistái külön kulcsot
  kapnak, nem törlik egymás hasznát. A cache nem tárol korábbi végleges ütemezési döntést.
- A lineáris domainképzés együtthatónként egyszer számít moduláris inverzet,
  nem a domain minden eleméhez külön. Modulus nélkül megmarad az egész osztás
  oszthatósági feltétele.

A heurisztikai szimuláció eredménye továbbra sem kerül K-ba, Deltába, E-be vagy
W-be bizonyított tényként. Az optimalizálás nem csökkenti a 256 jelöltvizsgálatot,
a feltételes körkorlátot vagy az SMT-kereteket; nem tartalmaz termékárhoz, változónévhez
vagy az ismert helyes tanúhoz kötött gyorsítást.

## Cache-Korlátok

| Cache | Megőrzési korlát |
| --- | --- |
| Kifejezéscache | Legfeljebb az első 1024 kifejezés, külön következtetési és értékelési bejegyzéssel |
| Egy kifejezésbejegyzés | Legfeljebb 4096 cella/érték tárolási egység |
| Kifejezéstábla | Legfeljebb 65536 tárolási egység, táblánként |
| Refinement pontozás | Egy aktuális probléma/K/Delta-pillanatkép és legfeljebb 128 cella–céllista pár kiszámított haszna |

Az egységek nem bájtok és nem szemantikai domainméret-korlátok. Ha egy cache
nem tud tárolni, a rendszer az eredeti számítást végzi el: nem csonkít domaint
és nem vesz el következtetési lehetőséget. A kifejezéscache a propagációs futás,
a pontozási cache a domainkeresési állapot élettartamához kötött; másik elemzés
nem használja az előző elemzés cache-ét.

A refinement pontozási cache külön kikapcsolható összehasonlító méréshez:

```bash
HALO2_ANALYZER_REFINEMENT_CACHE=0 cargo test --offline -p korrekt --lib thesis_invoice_recovery_smoke -- --ignored --nocapture --test-threads=1
```

Ez a kapcsoló a kifejezésszintű cache-t nem kapcsolja ki. A solverhívásokat
a közös kimeneti fájlok miatt minden mérésben sorosan kell futtatni.

## Ellenőrzés

A teljes könyvtári tesztkészlet sorosan lefutott: **470 sikeres, 0 hibás,
10 szándékosan kihagyott teszt**, 164,17 másodperc alatt. A regressziók között
szerepel a cache-elt és a közvetlen feltételes következtetés összehasonlítása,
a cellaazonosság és teljességi jelölés kezelése, a váltakozó céllisták és a
változó solverkeret, valamint a domainosztás kimerítő kis testes ellenőrzése.

## Elvetett Prototípus

A teljes UCP-szimulációk általános LRU-cache-ével végzett köztes próba 386,05
másodpercre rövidítette a korábbi 560,53 másodperces futást, azonos 63
SMT-hívással és ugyanazzal a részleges eredménnyel. A profil szerint azonban
2441 szimulációra csak 15 találat jutott, 2420 bejegyzéscserével. A refinement
pontozása önmagában közel 160 másodperc maradt. Ezt a nagyobb állapotokat tároló
prototípust ezért nem tartalmazza a végleges kód: a kisebb, célzott haszon-cache
váltotta fel. A 386,05 másodperc nem a végleges változat mérési eredménye.
