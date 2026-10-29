# Többfázisú Elszámolási Audit

A tests/demos/settlement_audit_demo_tests.rs egy szintetikus benchmarkcsalád.
Valódi Halo2-kapcsoláson futtatja a tényleges recovery pipeline-t.
Nem módosítja az elemző szabályait, ütemezését vagy solverkezelését a példa kedvéért.
A referencia csak a teszt eredményét ellenőrzi, nem elemzési premissza.

A dolgozat összefüggő vállalati számlapéldája külön circuit:
[`thesis_examples/invoice_circuit.rs`](../korrekt/src/circuit_analyzer/ucp/thesis_examples/invoice_circuit.rs).
Az új általános lineáris/intervallumos következtetéssel abban az UCP már
16 konkrét célértéket visszaállít. Az alábbi technikai benchmark továbbra is
az SMT-ből visszacsatolt domain utáni új UCP-fázist szemlélteti; a két példát
és a méréseiket nem szabad összekeverni.

## Kapcsolás

A rendszer egy privát elszámolás publikus összesítőit ellenőrzi:

~~~text
2*a + b = 190
a + 3*b = 170
amount + mask = 373
code^2 - 10*code + 21 = 0
fee + other_fee = 100
plan = 1
~~~

A tarifakódhoz tartozó code*(10-code) összesítő értéke publikus, de maga a kód nem.
A kapcsolás a polinom kifejtett alakját tartalmazza, nem a {3,7} gyökhalmazt.

További feltételek:

- Az amount kilenc logikai számjegyből áll, tehát 0..511 közé esik.
- A szivárgó változatban mask*(code-5)=0, ahol az 5 nyilvános fixed érték.
- A kezdeti kódkorlát opcionálisan 0..15; nélküle domainfelderítés vizsgálható.
- A fee katalógusa {10,20,...,90}, az other_fee katalógusa {20,40,60}.
- A korrelált (route,plan) lookup sora {(0,0),(1,0),(2,1),(3,2)}.
- Négy elosztási cella összege a; mindegyikre bucket_i*(route-i)=0.
- Az a, b és amount értékek másolási kényszerekkel másik sorhoz kapcsolódnak.
- Az első auditcél az előző sorból t0=a*amount+b, majd t_(i+1)=2*t_i+1.
- A kapuk szelektorokat, fixed értékeket és előző soros rotációkat használnak.

A bitméret és az auditlánc hossza külön fordítási paraméter: 9..16 bit és 1..16 láncelem.
Már a 9 bites kezdeti összegtartomány sem fér bele a 256 elemű explicit domainkorlátba.
Az elemző nem kapja meg előre az összeg jelöltjeinek rövid listáját.

## UCP, Majd SMT, Majd UCP

Az önálló UCP-teszt solverhívás nélkül ellenőrzi az első fixpontot:

| Rész | Első UCP-eredmény |
| --- | --- |
| Lineáris rendszer | a=80, b=30 |
| Korrelált lookup | route=2 a publikus plan=1 alapján |
| Kiválasztási minta | buckets={0,0,80,0} |
| Számjegyek | Mindegyik lefedő domainje {0,1}, konkrét érték nélkül |
| Katalógusok | fee in {40,60,80}, other_fee in {20,40,60} |
| Tarifakód | Legfeljebb a kezdeti 0..15 lefedő domain |
| Maszk, összeg, auditlánc | Még nem állítja vissza őket |

A teszt külön ellenőrzi, hogy a teljes tuple-reláció elhagyásakor a külön
oszlopvetületek nem rögzítik a route értékét. Az All-But-One-0 minta
alkalmazhatóságát konkrét értékek nélkül, a ténylegesen igazolt K-tényekkel is vizsgálja.
Egy eredményt több szabály is igazolhat; ez nem kizárólagos szabályattribúció.

A szűkítési profil letiltja a szemantikai gyorspróbákat és a domainfelderítést.
Az SMT-vel code in {3,7} lefedő halmazt állapít meg. Ezután az UCP felismeri,
hogy code-5 biztosan nem nulla, tehát mask=0. Ebből amount=373 lesz,
majd a bitek, a másolt cellák és az auditlánc értékei is visszaállnak.
A mask=0 és amount=373 állítás nem szerepel eredeti kényszerként.

Négy auditcél mellett a végső eredmény:

~~~text
amount = 373
mask = 0
code in {3,7}
fee in {40,60,80}
other_fee in {20,40,60}
t0 = 29870
t1 = 59741
t2 = 119483
t3 = 238967
~~~

A 25 kijelölt célból 22 pontos érték, 3 pedig többértékű teljes domain.
Az első fixpontban csak 7 kijelölt cél értéke ismert. A belső állapot ezen felül
publikus és fixed cellákat is tartalmaz; azok nem számíthatók bele a 25 célba.
A teljes privát értékadás nem egyértelmű: a kód két és a katalóguspár három
különböző megoldása ugyanazokat a megfigyeléseket adja.

## Ellenőrzések És Kontroll

A tesztek MockProverrel ellenőrzik az összes 2*3 érvényes kód/katalógus-kombinációt,
a hosszabb láncot és a szélesebb összegtartományt. Elutasítják a hibás kódot
és az elrontott összeget. Igazolják az első UCP elakadását és az SMT utáni új
propagációt. A szűkítési profilban az összeg, maszk és auditcél nem kap saját
SMT-keresést. Kezdeti kóddomain nélkül a tényleges domainfelderítés is lefut.

Másik helyes privát értékadással ugyanazok a domainek állnak elő.
A fő állításokat friss SMT-kódolásból függetlenül validálja; a hamis code={3}
állítást az eredeti kontextus ellenpéldájával cáfolja.
Ez instanciaellenőrzés és regressziós lefedettség, nem formális implementációverifikáció.

A kontrollváltozat csak a mask*(code-5)=0 kényszert hagyja el.
Az amount=373,mask=0 és amount=376,mask=-3 értékadások ugyanazokat a publikus
megfigyeléseket adják. A MockProver mindkét teljes értékadást ellenőrzi.

A kontroll recovery futása a jelenlegi 5 másodperces hívásonkénti kerettel
már a kezdeti SAT-vizsgálatnál bizonytalan lehet. Ez nem titkossági bizonyíték.
A nemegyértelműség referenciabizonyítékát a két ellenőrzött értékadás adja,
nem az elemző sikertelen keresése. A pozitív teszt sem kerüli meg az eredeti
SAT-ellenőrzést MockProverrel.

A példa nem modellez titkosítást vagy egy termelési protokoll teljes biztonságát.
A numerikus méret és a lánccellák száma nem kriptográfiai biztonsági bitszám.

## Futtatás És Mérés

A normál visszaállítás első UCP-futása már a publikus értékekkel indul.
A publikus értékek nélküli szerkezeti baseline nem kötelező előkészítés:
csak `PrivacyAnalysisOptions { compute_structural_baseline: true, ..Default::default() }`
esetén, a keresés után fut le. Ez külön riportkontroll, nem új keresési premissza.
A `structural_baseline_computed=false` jelzésnél a baseline-mezők üresek;
a nulla baseline-szűkülési számláló nem jelent sikertelen visszaállítást.

~~~bash
cargo test --offline -p korrekt --lib settlement_audit_ -- --nocapture --test-threads=1
~~~

A tesztek többször hívják az SMT-t, ezért nem pillanatnyi egységtesztek.
A SETTLEMENT_BEGIN az induló profilt, a SETTLEMENT a mérőszámokat,
a SETTLEMENT_VALUES a fő értékeket jelzi. A futtatás mindig soros legyen,
mert az elemző jelenleg közös SMT-fájlokat használ.

Az opcionális mérési mátrix:

~~~bash
UCP_SETTLEMENT_REPEATS=3 UCP_SETTLEMENT_CASE=small \
cargo test --offline -p korrekt --lib settlement_audit_measurement_matrix \
  -- --ignored --nocapture --test-threads=1
~~~

Az UCP_SETTLEMENT_CASE lehet small (9 bit, 4 lánc), chain (9 bit, 12 lánc),
wide (12 bit, 4 lánc), unseeded (9 bit, 4 lánc, kezdeti kóddomain nélkül), vagy all.
A chain, wide és unseeded eset a small változathoz képest rendre csak a lánchosszt,
a bitméretet vagy a kezdeti kóddomain rendelkezésre állását módosítja.
Az UCP_SETTLEMENT_PROFILES vesszővel szűrhető: propagation, fast, refinement,
discovery, combined. Alapértéke all; smt-only esetén csak az alapvonal fut.

A trial=0 bemelegítés, nem része a mediánoknak. Az önálló SMT-alapvonal ugyanazokat
a célokat kérdezi le UCP-tények és visszacsatolás nélkül. Nem sorolja fel a
többértékű domaineket, ezért az idő mellett a kapott információt is össze kell vetni.
A propagation profil a publikus API-t használja, tehát tartalmazza a kezdeti
SAT-ellenőrzést; a solver nélküli UCP-t külön teszt mutatja be.

| Mérőszám | Jelentése |
| --- | --- |
| smt_invocations | Tényleges solverindítások, SAT-ellenőrzéssel és sikertelen próbákkal együtt |
| semantic_attempts | Szemantikai cellapróbák, nem közvetlen solverhívásszám |
| refinement_checks | Lefedés- és jelöltellenőrzések |
| discovery_checks | Értékfelsorolás és kizárási ellenőrzések |
| propagation_runs | A recovery UCP-futásai, a kezdeti SAT-jelöltszámítás nélkül |
| exact, finite, complete | Pontos értékek, többértékű domainek és teljes domainek száma |
| status, unknown | Befejezetlenség és solverkorlátok, amelyeket nem hagy ki az eredményből |
| elapsed_ms | Teljes API-idő, a független validálás nélkül |

A nagyobb változatoknál a részleges és bizonytalan eredmény is mérési eredmény.
A teszt nem feltételezi, hogy minden profil ugyanazt az információt adja vissza,
és nem állít kötelező gyorsulási arányt.

## Első Helyi Mérés

2026-10-29-én a small változat azonos 5 másodperces hívásonkénti időkorláttal,
egy bemelegítés és egy mért ismétlés mellett ezt adta:

| Profil | Pontos célérték | Teljes domain | Solverindítás | API-idő |
| --- | --- | --- | --- | --- |
| Propagation, SAT-kapuval | 7 | 7 | 1 | 1,845 s |
| Refinement | 22 | 25 | 29 | 10,622 s |
| Combined | 22 | 25 | 33 | 22,509 s |
| Önálló SMT | 22 | nem sorolja fel | 51 | 56,846 s |

A visszaállított 22 érték mindhárom sikeres profilban azonos; az SMT-alapvonal
a további három cél nemegyértelműségét is megállapította, de nem adott teljes
többértékű domaineket. A Refinement és Combined profil 3 UCP-futást végzett.
A két hibrid profil tehát több domaininformáció mellett is kevesebb solverhívást
használt ezen az instancián, de a Combined profil nem volt jobb a Refinementnél.
Ez ellenőrzött példaeredmény, nem több ismétlésből számított teljesítményállítás.
A dolgozati méréshez több ismétlés és a nagyobb változatok külön eredménye szükséges.
