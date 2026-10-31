# A dolgozat összefüggő példái

Ez a mappa az `ucp/tests` testvére. Kizárólag tesztfordításkor kapcsolódik be;
nem módosítja a működő elemző szabályait vagy a keresési heurisztikáját.
A korábbi demonstrációkat és regressziós teszteket nem helyettesíti.

## Egységes Alapkonfiguráció

Mindegyik számlaváltozat ugyanabból a `recovery_options` függvényből kapja a
teljes konfigurációt: fast probe, domainszűkítés és domainfelderítés is
engedélyezett. Az ütemező az aktuális tudás alapján választ; a példa neve,
publikus értéke vagy elvárt eredménye nem kapcsol ki keresési lehetőséget.
Az alapkeretek: 256 szemantikai próba, 160 szűkítési solverhívás és 64 felderítési
solverhívás, legfeljebb 128 szűkítési jelölt és 16 felderítési minta cellánként.
A hívásonkénti keret 3000 ms; az újrapróbálkozás sem kap automatikus hosszabbítást.

Az alapértelmezett jóváhagyásos profil `standard`; a `combined` ugyanennek
kompatibilis neve. A `refinement` kifejezetten komponens-kikapcsolásos kontroll,
nem a dolgozat teljes algoritmusának alapbeállítása. Az alap számla mérési
mátrixában a `propagation`, `fast`, `refinement` és `discovery` szintén ilyen
kontrollprofilok. Mindegyik ugyanazt a futtató algoritmust használja.

Az összkeretek közösen állíthatók: `UCP_INVOICE_SEMANTIC_QUERIES`,
`UCP_INVOICE_REFINEMENT_CHECKS`, `UCP_INVOICE_DISCOVERY_CHECKS` és
`UCP_INVOICE_DISCOVERY_VALUES`. A standard keretei pozitívak; a kontrollprofil
ezután tiltja le a nem vizsgált komponenseket.

## Korábbi Mérések

A lentebbi futásadatok a feltüntetett korábbi konfigurációkhoz tartoznak,
nem az új egységes standard alapbeállítással végzett új mérések.

A [snapshot-alapú fast probe](../../../../../docs/seeded-fast-probes.md) már
W-mintából is indul, és más célok modellértékeit is megosztja. Új egyszeri
release-próbák: alap invoice combined 0,69 s / 7 hívás / 19 teljes domain;
H=21 combined 2,62 s / 16 hívás / 21 teljes domain; díjkatalógusos H=25
combined, 160-as kerettel 261,86 s / 138 hívás / 21 teljes domain.
A lentebbi v8 és korábbi mérések történeti összehasonlítások.

A jelenlegi refinement a [teljes SAT-modellek más célcellákhoz tartozó mintáit](../../../../../docs/shared-model-samples.md)
is újrahasználja. A lentebbi lefedés-újrahasználati és régebbi futásadatok
korábbi keresési szabályzatok egyszeri mérései; nem a mintamegosztás mérései.
Az új egyszeri release-próbák: alap invoice 0,74 s / 10 hívás / 19 teljes domain;
H=21 invoice 2,43 s / 16 hívás / 21 teljes domain; díjkatalógusos H=25 kontroll
89,33 s / 48 hívás / 18 teljes domain, még részleges eredménnyel.

**Új, visszacsatolásos változat:** a [jóváhagyáshoz kötött kézi felár](../../../../../docs/invoice-approval-demo.md)
a számla egészéhez kapcsolódik. Az első UCP 5 pontos célértéket talál, az SMT
a mód domainjét szűkíti, a következő UCP pedig további 12 értéket állít vissza.
Külön többértelmű kontroll és független referencia tartozik hozzá.
Ennek teljes UCP--SMT recovery-tesztje is futtatható azonos profilokkal:

```bash
cargo test --release -p korrekt --lib thesis_invoice_approval_control_recovery -- --ignored --nocapture --test-threads=1
```

A szűkebb, `a in {0,432}` díjkatalógusos kontroll két különböző kosarat enged.
A széles kontroll megtartása mellett külön kapcsolás- és teljes recovery-tesztje van:

```bash
cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_reference_and_mock_prover -- --nocapture --test-threads=1
cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_recovery -- --ignored --nocapture --test-threads=1
```

A refinement összkerete a teszt futtatásakor is megadható. A korábbi mérésekben
48 volt, a standard konfigurációban 160 az alapértéke. Például explicit 160
hívásos keret, csak szűkítést engedő kontroll és 3000 ms/hívás időkorlát:

```bash
UCP_INVOICE_APPROVAL_PROFILE=refinement UCP_INVOICE_REFINEMENT_CHECKS=160 UCP_INVOICE_TIMEOUT_MS=3000 cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_recovery -- --ignored --nocapture --test-threads=1
```

Ez az egyszeri release-próba sikeres: 134 tényleges hívás, 249,35 s,
9 pontos célérték és 12 többértékű domain, mind a 21 teljesnek igazolt;
12 cél bizonyítottan nem egyedi, ismeretlen egyértelműségű cél nincs.
A [részletes mérés](../../../../../docs/shared-model-samples.md)
a 48-as és 160-as keretet azonos időkorláttal hasonlítja össze.

A [kis domainekkel segített keresés](../../../../../docs/domain-assisted-search.md)
ennek egyszeri release-idejét 104,46 s-ról 88,92 s-ra csökkentette azonos keretekkel,
és a kupon nemegyértelműségét is bizonyította. A teljes domainigazolás még részleges;
ez nem általános vagy ismételt gyorsulási mérés.

Az alábbi 16 pontos értékes mérések az eredeti, felár nélküli számlára vonatkoznak.
A feláras változat korábbi [általános ütemezési gyorsítása](../../../../../docs/premise-guided-refinement.md)
az újramért teljes időt 69,56 s-ról 27,66 s-ra, a solverhívások számát 27-ről
14-re csökkentette azonos keretekkel. Ez egyszeri összehasonlítás, nem általános garancia.

**Korábbi, a Delta lefedését már újrahasználó, de modellmintákat még nem megosztó release-próbák:** alap invoice
0,81 s / 14 hívás / 19 teljes domain; H=21 feláras számla
2,59 s / 24 hívás / 21 teljes domain. A [részletes leírás](../../../../../docs/established-domain-refinement.md)
a díjkatalógusos kontroll erősebb, de továbbra is részleges eredményét is megadja.
Ezek egyszeri mérések, nem ismételt benchmarkok.

**Korábbi, kis domainekkel segített, de lefedést újraellenőrző release-próbák:** alap invoice 1,05 s,
16 hívás és 19 teljes domain; H=21 feláras számla 2,90 s, 28 hívás és 21 teljes
domain. A [részletes leírás](../../../../../docs/domain-assisted-search.md)
az export helyességi feltételeit és a díjkatalógusos kontroll fennmaradó korlátait
is megadja. Az alábbi 1,72 s és 4,11 s a korábbi, csak pontos tényeket használó
verzió egyszeri release-mérése, nem a jelenlegi változaté.

**Korábbi, csak pontos tényeket használó release-próba:** a lefedésvizsgálatok a többi kereséshez hasonlóan
újrahasználják a már igazolt pontos tényeket. A felár nélküli számla az alapértelmezett
3000 ms/hívás kerettel 1,72 s alatt, 16 solverhívással futott le: UCP 0,48 s,
SMT 1,20 s, egyéb munka 0,03 s (kerekített részidők). A 16 pontos célérték és
három többértékű domain változatlan, de most mind a 19 domain teljesnek igazolt.
A 60 s/hívás kerettel, pontos tények nélküli lefedéssel végzett korábbi release-próba
120,69 s alatt sem igazolta a két beszállítói domain teljességét. Ezek egyszeri
futások, nem ismételt benchmarkok; a korábbi debugidőkkel nem képeznek gyorsulási arányt.
A külön riportvalidálás továbbra sem feltételezi a visszaállított pontos értékeket.
A feláras számla új `refinement` release-próbája szintén sikeres: 4,11 s,
28 hívás, 17 pontos érték és mind a 21 cél-domain teljes. A kezdeti SMT-kizárást
követő UCP-visszacsatolás változatlanul megmaradt.

**Korábbi debugmérés, pontos tények nélküli lefedéssel:** az általános lineáris/intervallumos következtetéssel a
számlapélda már sikeresen visszaállítható. Az önálló UCP a végső új mérésben
4,22 másodperc alatt 16 konkrét célértéket és a három fennmaradó cél helyes
véges vetületét állította elő. A teljes elemzés akkori futása 10,52 másodperc,
8 SMT-hívás és `Analyzed` eredmény volt. Az alábbi korábbi timeoutos mérések
fejlesztési előzmények; nem a jelenlegi következtetési képességet jellemzik.
A teljes futás egyetlen normál, publikus értékekkel indított UCP-elemzést
végzett, 4,08 s alatt; a solverfolyamatok együtt 6,15 s időt használtak.
A korábbi, 66,11 s-os futás kötelező szerkezeti baseline-t is számított.
Ez a kontroll most alapértelmezetten kikapcsolt, ezért nem terheli a rendes keresést.

Az akkori teljes elemzés a kupont és a két beszállítói részt helyesen `NonUnique`
eredménnyel jelenti. Összesen 17 cél-domain teljesnek igazolt: a 16 singleton
és a kupon kétértékű domainje. A beszállítói domainek megfelelnek a független
referenciának, de abban a riportban még nem voltak teljesnek tanúsítottak. Az `Analyzed`
nem jelenti minden cél-domain teljességi bizonyítványát.

Az új szabály [leírása](../../../../../docs/ucp-relational-propagation.md) és
a [végső mérés](../../../../../docs/ucp-performance.md) részletezi az általános
eliminációt, a körbefordulás ellenőrzését és a teljes, korlátos sorvizsgálatot.
A circuit, a tanúkezelés és a keresési beállítások változatlanok maradtak.
Az első új teljes próba 66,98 s volt; az ezt követő domainmásolási gyorsítás
utáni 66,11 s nem külön statisztikai sebességmérés. A regressziós készlet
476 sikeres, 0 hibás és 10 szándékosan kihagyott teszttel zárult a baseline
opcionálissá tétele előtt.

Külön szerkezeti összehasonlításhoz a hívó
`PrivacyAnalysisOptions { compute_structural_baseline: true, ..Default::default() }`
beállítást adhat meg. A kontroll csak a keresés után fut, nem ad premisszát
az SMT-nek vagy az UCP-nek. A normál riportban
`structural_baseline_computed=false`, a baseline-domainek hiányoznak és a
baseline-szűkülési számláló nulla; ez nem jelent hiányzó visszaállított értékeket.
A jelenlegi verzió teljes könyvtári regressziója 479 sikeres, 0 hibás és
10 szándékosan kihagyott teszt, 164,51 s alatt.

## Vállalati kosár és számla

A vállalat négy ismert terméktípusból vásárol. A circuit igazolja a számla
helyességét, de nem publikálja a termékmennyiségeket, a kuponosztályt vagy
a papíráru beszállítói megosztását. A mennyiségek 0 és 127 közötti egészek.

| Termék | Nettó egységár | Tömeg (g) | Hűségpont |
| --- | ---: | ---: | ---: |
| Papíráru | 1200 | 500 | 2 |
| Kávé | 2500 | 1000 | 5 |
| Tisztítószer | 1800 | 700 | 4 |
| Kábelcsomag | 900 | 200 | 1 |

Az árak egész pénzegységek. A 20%-os adó és a díjszabás kitalált példaszabály,
nem tényleges adójogi vagy fizetési specifikáció.

### Kényszerek

1. A termékmennyiségeket hét logikai bitből állítja össze.
2. A sorértékeket a mennyiség és a fixed oszlopba írt ár, tömeg, pont
   szorzataként számítja. Ezeket rotációkkal összegzi N, W, P, B értékekké.
3. A korrelált kuponlookup `(c,d)` párjai: `(0,0), (1,5), (2,10), (3,10),
   `(4,15)`. A kuponosztály nem egyedi kuponazonosító vagy aláírás.
4. A kedvezmény: `100 D + r_D = d B`, `0 <= r_D < 100`.
5. A kezelt nettó összeg: `E = B - D + 17`.
6. Az adó: `100 V + r_V = 20 E`, `0 <= r_V < 100`.
7. A tömeg szerinti korrelált szállítási lookup:
   `(k,L,U,S) = (0,0,50000,600), (1,50001,100000,1200),
   (2,100001,200000,2000)`. Az `L <= W <= U` feltételt két nemnegatív
   különbséggel írja elő. A szállítási díj külön, adó utáni bruttó díj.
8. A végösszeg: `G = E + V + S`.
9. A papíráru két beszállítótól érkezik: `q_1 = u + v`, ahol
   `u in {0,2,...,60}` és `v in {0,3,...,63}`.
10. A könyvelési felosztás: `S_0 + S_1 + S_2 = S`, `S_i (k-i) = 0`.
    Ez három köztes könyvelési érték, nem három további független titok.

A kedvezményt, adóalapot, adót és a két tömegkülönbséget öt hexadecimális
számjegyből állítja össze; a számjegyeket 0..15 lookup korlátozza. Így ezek 20 bites
nemnegatív egészek. A katalógus és a mennyiségi korlát alapján `B <= 812800`,
`d B <= 12192000`; a többi egész művelet is messze a Halo2 skalártestének
modulusa alatt marad. A maradékok korlátja valódi egész osztási/kerekítési
szemantikát biztosít. Nem csak mezőbeli egyenletekkel feltételezi a tartományokat.

### Publikus megfigyelések és referencia

`N=124`, `W=71600`, `P=352`, `G=208148` mellett az egyetlen kosár:

`(q_1,q_2,q_3,q_4) = (37,29,25,33)`.

Ekkor `B=191600`, `d=10`, `D=19160`, `r_D=0`, `E=172457`, `V=34491`,
`r_V=40`, `k=1`, `S=1200`. Ugyanakkor a kupon `c in {2,3}` marad,
és a beszállítói párok:

`(u,v) in {(4,33),(10,27),(16,21),(22,15),(28,9),(34,3)}`.

Ez 12 különböző privát bemeneti kombináció ugyanazon megfigyelések mellett.
A beszállítói domainek vetületei nem jelentik a két halmaz Descartes-szorzatát.

| Rögzített megfigyelések | Különböző kosarak |
| --- | ---: |
| N | 325618 |
| N,W | 772 |
| N,W,P | 55 |
| N,W,P,G | 1 |
| W,P,G | 10 |
| N,P,G | 28 |
| N,W,G | 14 |

A darabszámok a négy termékmennyiség különböző értékadásait számolják,
nem a kupon, beszállítói bontás vagy segédcellák összes kombinációját.
A számlaszabályok minden változatban megmaradnak; csak a publikus rögzítések
változnak. Egy megfigyelés elhagyása nem egy számítási kapu törlését jelenti.

## Források

| Fájl | Szerep |
| --- | --- |
| `invoice_circuit.rs` | Halo2 configure/synthesize, tanúadatok és cellaazonosítók |
| `invoice_reference.rs` | Külön egészszámos referenciamodell, teljes bemeneti enumeráció |
| `invoice_tests.rs` | MockProver, referenciák, tiszta UCP és választható SMT-mérések |
| `invoice_approval_tests.rs` | Jóváhagyási felár, független referencia, többértelmű kontroll és valódi SMT-visszacsatolás |

A riport céljai a négy mennyiség, a privát számla-köztesértékek, a kupon,
a beszállítói bontás és a könyvelési részösszegek. A már publikált bruttó
végösszeget nem számolja visszaállított privát értéknek.

A referenciaszámítás csak az eredmények ellenőrzésére szolgál. Nem írja be a
megoldott mennyiségeket, levezetett összefüggéseket vagy a konkrét B értéket
az elemző premisszái közé. A mérés a nyilvános
`analyze_private_recoverability_with_witness` belépési pontot használja.
Ez a teljes tényleges tanút az elemzés publikus megfigyeléseivel ellenőrzi;
csak sikeres MockProver-ellenőrzés helyettesíti a kezdeti SMT-s létezéskeresést.
A tanúértékeket nem adja át a visszaállításnak. Sikertelen vagy hiányos tanúnál
megmarad az SMT-s fallback; a hibás tanú önmagában nem jelent UNSAT-ot.

## Futtatás

Gyors referencia- és kapcsolástesztek:

```bash
cargo test --offline -p korrekt --lib thesis_invoice_reference -- --nocapture --test-threads=1
cargo test --offline -p korrekt --lib thesis_invoice_mock -- --nocapture --test-threads=1
```

Az UCP-fixpont külön, solver nélkül:

```bash
cargo test --offline -p korrekt --lib thesis_invoice_ucp -- --nocapture --test-threads=1
```

Egyetlen, bemelegítés nélküli teljes elemzési próba:

```bash
cargo test --offline -p korrekt --lib thesis_invoice_recovery_smoke -- --ignored --nocapture --test-threads=1
```

A hosszabb, választható mérés egy bemelegítést és alapértelmezés szerint
három rögzítendő ismétlést végez profilonként:

```bash
UCP_INVOICE_PROFILES=combined UCP_INVOICE_REPEATS=1 \
cargo test --offline -p korrekt --lib thesis_invoice_measurement_matrix -- --ignored --nocapture --test-threads=1
```

Profilok: `propagation`, `fast`, `refinement`, `discovery`, `combined`, illetve
`all`. A `propagation` profil is tartalmaz kezdeti létezésellenőrzést:
helyes tanúnál MockProvert, egyébként SMT-s fallbacket. Nem azonos a külön,
solver és tanúellenőrzés nélküli fixpontteszttel.
Az `UCP_INVOICE_TIMEOUT_MS` egy solverhívás időkerete, alapértéke 3000 ms;
ez a későbbi visszaállítási keresésekre vonatkozik. A kezdeti SAT-vizsgálat
külön `UCP_INVOICE_INITIAL_SAT_TIMEOUT_MS` keretet kap, alapértéke 60000 ms.
A jelenlegi helyes tanúval ezt a keretet nem használja el, mert a MockProver
igazolja a létezést; csak az esetleges SMT-s fallbackre vonatkozik.
A SAT-vizsgálat után a rendszer visszaállítja a keresések rövidebb időkeretét.
Mindkét érték solverhívásonkénti korlát, nem teljes futásidőkorlát; egy
esetleges SAT-jelöltpróba és az eredeti kontextusú fallback külön hívás.
A méréseket a közös SMT-kimeneti fájlok miatt
sorosan kell futtatni.

A napló külön mutatja a tényleges SMT-folyamatindításokat, szemantikai
próbákat, domainellenőrzéseket, UCP-futásokat, időt, domaineket és teljességet.
Alapértelmezetten a [tömör fázisnapló](../../../../../docs/private-recovery-phase-report.md)
jelenik meg: `1. UCP`, majd az egymást követő SMT-műveleteket összefogó `1. SMT`.
A mennyiségek és a számla célcellái olvasható nevet kapnak. Csak valós
új propagációnál jelenik meg `2. UCP`; ebben a példában jelenleg nincs ilyen.

A részletes profilozás és a korábbi gépi sorok kapcsolója:

```bash
UCP_DEMO_VERBOSE=1 cargo test --offline -p korrekt --lib thesis_invoice_recovery_smoke -- --ignored --nocapture --test-threads=1
```

Ebben a részletes nézetben az `INVOICE_SAT evidence=Some(VerifiedWitness)` sor jelzi a tényleges tanúellenőrzést;
ilyenkor `sat_checks=0`. Ez nem a SAT-előfeltétel ellenőrizetlen kihagyása.
Az `INVOICE_BASELINE computed=false` sor jelzi a rendes, külön szerkezeti
kontroll nélküli futást; a profilon egy normál `ucp.propagation` szerepel.
Az időkorlátos/részleges eredmény is mérési eredmény, nem sikeres visszaállítás.
A számlából következő matematikai egyértelműség nem garantálja, hogy a jelenlegi
szabályok és keretek a teljes visszaállítást ténylegesen el is végzik.

## Ellenőrzött állapot

A tanúellenőrzés hozzáadása előtti, 2026-10-29-i fejlesztési futásban a külön referenciák és a MockProver-tesztek
sikeresek voltak. A teljes könyvtári tesztkészlet 452 sikeres, 0 hibás és
10 szándékosan kihagyott teszttel zárult, sorosan körülbelül 232 másodperc alatt.
A tiszta UCP-fixpont a hexadecimális tartománykódolással
debug fordításban körülbelül 47 másodpercet igényelt. A mennyiségek és a
számla privát értékei nem váltak konkréttá; a kezdeti covering domainek megmaradtak.

A korábbi, közös 3000 ms-os solveridőkerettel végzett kombinált próba a kezdeti SAT-kérdésnél
`SolverUnknown / SolverTimeout` eredménnyel zárult: egy solverhívás történt,
szemantikai próba, domainszűkítés, domainfelderítés és riportálható UCP-fázis
még nem indult. A teljes idő megközelítőleg 50 másodperc volt, mert a SAT-ot
megelőző jelöltszámítás UCP-t is futtat. A timeoutos riport üres domainjei
nem jelentik azt, hogy a külön lefuttatott UCP semmilyen domaint nem tud előállítani.
A külön, 60000 ms-os kezdeti kerettel végzett SMT-s próba is a kezdeti SAT-nál
timeoutolt, körülbelül 107 másodperc teljes idővel. Ezek a korábbi eredmények
az SMT-alapú belépési pontra vonatkoznak, nem a később bevezetett tanúellenőrzésre.

A tanúellenőrzéses kombinált próba már végigfutott, egy fejlesztési ismétlésben:

| Mutató | Eredmény |
| --- | ---: |
| Létezési bizonyíték | `VerifiedWitness` |
| Kezdeti SMT-hívások | 0 |
| Összes tényleges SMT-hívás | 63 |
| Szemantikai próbák | 8 |
| Refinement solverhívások | 48 |
| Discovery solverhívások | 7 |
| Visszaállítási UCP-futások | 1 |
| Pontosan visszaállított célok | 0 |
| Rögzített nem egyelemű lefedő domainek | 12 |
| Teljesnek igazolt célcelladomainek | 0 |
| Állapot | `QueryLimitReached` |
| Teljes idő, debug fordítás | 560,53 s |

A 12 domain nem 12 sikeres SMT-s szűkítést jelent: a riport a már rendelkezésre
álló lefedő domaineket is tartalmazza. Új beolvasztható tény hiányában nem indult
második visszaállítási UCP-fázis. A kezdeti SAT-akadály megszűnt, a későbbi
keresések viszont továbbra is idő- és lekérdezési korlátokba ütköztek. Ez egy
egyszeri fejlesztési futás, nem ismételt teljesítménymérés vagy gyorsulási állítás.

A tanúellenőrzés hozzáadása után a privacy modul 69 célzott tesztje is sikeres:
ez 9 új tanúellenőrzési tesztet tartalmaz, többek között hibás és hiányzó tanúra,
eltérő publikus megfigyelésre, privát értékek át nem vételére, mezőbeli
reprezentációra és az önálló SMT-s domainvalidáció megőrzésére.

Ez a korábbi állapot ellenőrzött szemantikai példa és teljesítmény-stresszteszt
volt, nem igazoltan sikeres többlépcsős visszaállítási mérés. A tesztek az időkorlátos
riport állításainak helyességét is ellenőrzik; a sikeres tesztjelzés nem jelenti
automatikusan a titkos mennyiségek sikeres visszaállítását. A valódi
UCP → SMT → UCP visszacsatolás korábbi demonstrációja továbbra is a
`tests/demos/settlement_audit_demo_tests.rs` példában található.

## Profilozott Optimalizálás

Az általános cache- és aritmetikai gyorsítások után az egyszeri kombinált futás
236,08 másodpercre rövidült a korábbi 560,53 másodpercről. A 63 SMT-hívás,
a 0 pontos célérték, a 12 lefedő domain és a `QueryLimitReached` eredmény nem
változott. A futás most fázisonkénti `PROFILE` sorokat is kiír. A részletes mérés,
a cache-ek helyességi feltételei és a korlátok a
[teljesítményleírásban](../../../../../docs/ucp-performance.md) szerepelnek.
