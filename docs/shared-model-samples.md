# Teljes SAT-modellek Mintáinak Újrahasználata

A [fast probe egységesítése](seeded-fast-probes.md) a mintamegosztást már erre
a stratégiára is kiterjeszti, és meglévő W-értékkel kihagyja a kezdő modellkeresést.
Az alábbi mérési táblázatok a korábbi v8 állapotot rögzítik.

A refinement egy SAT jelöltellenőrzése nemcsak a vizsgált cella értékét
igazolja: a teljes modell többi cellájának értéke is megvalósítható ugyanazon
eredeti kényszerek és publikus megfigyelések mellett. A rendszer ezeket a
vetületeket is megőrzi a W mintahalmazaiban.

## Adatfolyam

1. A jelöltkérdés továbbra is a teljes eredeti kontextusból indul, az igazolt
   pontos értékek és kis lefedő domainek redundáns keresési állításaival.
2. Ugyanattól a solverfolyamattól lekéri a még nem teljes cél-domainek celláinak
   értékét és a vizsgált cella értékét. A másolati aliasok közös SMT-változót
   használnak. Nem indít külön hívást a többi értékért.
3. Csak SAT válasz után ad át mintákat. Hiányzó kért érték, hibás szám vagy
   eltérő testmodulus hibát jelent; UNSAT és UNKNOWN nem ad mintát.
4. Az új vetületek a megfelelő W(v) halmazba kerülnek, nem K-ba vagy Deltába.
   Két különböző érték nemegyértelműséget bizonyít. Meglévő lefedő domainnél
   az összes jelölt megvalósíthatósága teljességet igazolhat.
5. A teljesnek igazolt domaineket az ütemező kihagyja. Más cellák későbbi
   refinementje átveszi a már ismert mintákat, és nem kérdezi őket újra.

A W továbbra is cellánkénti vetületeket őriz meg: külön minták tetszőleges
kombinációja nem feltétlenül alkot közös kielégítő értékadást. Domain nélküli
cellához a minták nem hoznak létre lefedő domaint, egyetlen minta pedig nem
bizonyít pontos visszaállítást. A puszta új minták és teljességi jelölések nem
indítanak új propagációt. A teszttanú és a referencia nem elemzési premissza.

A változás a refinement teljes modellű jelöltellenőrzéseit érinti.
A részhalmazos keresésekből továbbra sem kerül át SAT-minta; a külön
független riportvalidálás változatlanul az eredeti kontextusban ellenőriz.
A domain discovery és a fast-probe meglévő mintavisszaadási útvonala megmarad.
A keresési szabályzat `shared-model-samples-refine-discover-v8`.

## Napló És Regressziók

A fázisnapló `Model samples: <cella>: <értékek>` sorai mutatják a más
cellákhoz újonnan megőrzött vetületeket. A strukturált
`RecoverySmtStep.model_samples` a teljes új listát tartalmazza; a szöveges
előnézet legfeljebb nyolc cellát és cellánként nyolc értéket jelenít meg.
Az így bizonyított teljesség és nemegyértelműség az adott SMT-lépés
állapotváltozásai között is megjelenik, de nem számít új vagy szűkebb domainnek.

A célzott tesztek két korrelált logikai cella teljes domainjét összesen két
jelöltkérdéssel igazolják, új UCP-kör nélkül. Egyetlen hívásnál egyik sem
minősül egyedinek vagy teljesnek. Külön regresszió ellenőrzi a domain nélküli
cél mintáinak kezelését, a másolati aliasokat, az UNSAT mintamentességét,
valamint a hiányzó és eltérő testű modellértékek elutasítását.

A teljes soros release könyvtári tesztkészlet 500 sikeres, 0 hibás és 13
szándékosan kihagyott teszttel zárult. A fordítási ellenőrzés minden targetre,
a módosított Rust-fájlok formázásellenőrzése és a diff whitespace-ellenőrzése
szintén sikeres. A korábbi, független logikai cellákat vizsgáló regresszió
legfeljebb három ellenőrzésből igazolja mindkét kételemű domaint, a korábbi
négy helyett; a korrelált esethez két hívás elegendő.

## Release-próbák

Azonos 3000 ms/hívás kerettel, a példák változatlan profiljaival végzett
egyszeri új futások:

| Példa | Korábbi hívásszám | Mintamegosztással | Új API-idő | Teljes cél-domainek |
| --- | ---: | ---: | ---: | ---: |
| Alap invoice, combined | 14 | 10 | 0,74 s | 19/19 |
| H=21 feláras invoice, refinement | 24 | 16 | 2,43 s | 21/21 |
| H=25 díjkatalógusos invoice, refinement | 48 | 48 | 89,33 s | 18/21 |
| Settlement, refinement | 23 | 19 | 2,30 s | 25/25 |

A díjkatalógusos változat előző, lefedést már újrahasználó futása 92,42 s,
15 teljes domain, 10 nem egyedi cél és 4 ismeretlen egyértelműségű cél volt.
Az új futás 18 teljes domaint és 12 nem egyedi célt igazol; 2 cél
egyértelműsége marad ismeretlen. Mindkettő 7 pontos értéket és 14 többértékű
domaint jelent. A négy kosármennyiség, termékösszeg, kedvezmény, adóalap és adó
kételemű domainjei, valamint a felár kételemű domainje összesen két kosárjelölt
SAT-modelljéből teljessé válnak. A beszállítói v teljességét az u vizsgálatának
modelljei igazolják, külön v-jelöltkérdések nélkül.

A kupon, kedvezményszázalék és kedvezménymaradék domainje még nem teljes.
A korábbi hívások megtakarítása után maradó keret további maradékjelöltek
kizárására fordul; a 48 hívásos összkeret elfogy, a végállapot továbbra is
`QueryLimitReached`. Egyes jelöltkérdések timeoutolnak. A mintamegosztás
ezért erősebb eredményt ad ugyanabból a keretből, de nem oldja meg önmagában
a nehéz kizárási kérdéseket. Az időadatok egyszeri futások, nem ismételt
benchmarkok vagy általános gyorsulási garanciák.

## Nagyobb Híváskeret: 160

A díjkatalógusos kontroll ugyanazzal a 3000 ms/hívás időkorláttal, kizárólag
a refinement összkeretét 160-ra emelve teljes eredményt adott:

| Mutató | 48 hívásos keret | 160 hívásos keret |
| --- | ---: | ---: |
| Tényleges solverhívások | 48 | 134 |
| API-idő | 89,33 s | 249,35 s |
| Pontos célértékek | 7 | 9 |
| Többértékű cél-domainek | 14 | 12 |
| Teljes cél-domainek | 18/21 | 21/21 |
| Bizonyítottan nem egyedi célok | 12 | 12 |
| Ismeretlen egyértelműségű célok | 2 | 0 |
| Végállapot | QueryLimitReached | Analyzed |

A kedvezménymaradék 99 még nem igazolt jelöltjének ellenőrzése kizárja az
összes nemnulla értéket, így a lefedő domain `{0}` lesz. Az új pontos tény
után a kedvezményszázalék három korábban timeoutolt jelöltjét is sikerül
kizárni, eredménye `{10}`. Az utolsó UCP-fázis ebből a kupon domainjét
`{2,3}`-ra szűkíti, amelynek mindkét értékét W már korábban igazolta.
Összesen négy UCP-fázis és három SMT-fázis történik; az SMT-fázisok hívásszáma
12, 119 és 3. A mintamegosztás és a korábbi igazolt értékek újrahasználata
végig aktív, külön utólagos SMT-validálás nem része ennek az időnek.

```bash
UCP_INVOICE_REFINEMENT_CHECKS=160 UCP_INVOICE_TIMEOUT_MS=3000 cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_recovery -- --ignored --nocapture --test-threads=1
```

A tesztsegéd alapértéke továbbra is 48 hívás. A nagyobb keret parancssorból
adható meg; nem változtatja meg a circuitet, az elemző szabályait vagy a többi
futás alapbeállítását. Ez szintén egyszeri release-próba, nem átlagolt mérés.

## Combined Profil Azonos Keretekkel

A külön combined próba ugyanazon circuiten, ugyanazzal a 160-as refinement-
kerettel és 3000 ms/hívás időkorláttal, legfeljebb nyolc fast-probe próbával futott:

| Mutató | Refinement | Combined |
| --- | ---: | ---: |
| Tényleges solverhívások | 134 | 139 |
| Refinement-hívások | 134 | 134 |
| Fast-probe próbák / solverhívások | 0 / 0 | 5 / 5 |
| API-idő | 249,35 s | 264,57 s |
| Pontos célértékek | 9 | 9 |
| Többértékű cél-domainek | 12 | 12 |
| Teljes cél-domainek | 21/21 | 21/21 |
| Bizonyítottan nem egyedi célok | 12 | 12 |
| Ismeretlen egyértelműségű célok | 0 | 0 |

Mindkét teszt sikeres, végállapotuk `Analyzed`. A combined ebben az egyszeri
futásban nem javított: az öt plusz próbálkozás mind timeoutolt. A vizsgált
cellák az adóalap, az adó, a kedvezményszázalék, a kedvezménymaradék és a
kupon voltak. A maradék 99 jelöltvizsgálata emiatt változatlanul lefutott.

A v8 fast-probe backend először új teljes modellt keres, és csak ennek
értékével fogalmazza meg a kizárási kérdést. Az öt próba egy-egy tényleges
hívásból állt: az első modellkeresés timeoutolt, a kizárási kérdésig nem jutott
el. A recoveryban már megőrzött W-minta nem váltja ki ezt a kezdő modellkeresést.
Ez elkülönül a jelöltenkénti refinementtől, amely már újrahasználja W-t.
Egy későbbi javítás közvetlenül az igazolt mintából indíthatná a kizárást;
ennek eredményességét külön kell mérni. Ez a mérés nem módosította az elemzőt.

```bash
UCP_INVOICE_APPROVAL_PROFILE=combined UCP_INVOICE_REFINEMENT_CHECKS=160 UCP_INVOICE_TIMEOUT_MS=3000 cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_recovery -- --ignored --nocapture --test-threads=1
```
