# Affin Visszavetítés Kis Véges Domainekből

A `finite_projection.rs` az egyenletenkénti domainkövetkeztetés része.
Ha a meglévő teljes lineáris alakfelismerés nem alkalmazható, célcellánként
megpróbál affin lefedést képezni. Az egyenlet más cellákban nemlineáris is
lehet: például `c*x + y*z = 0` feldolgozható, ha a szükséges domainek végesek.
Lookup-bemenet esetén a nulla helyett a teljes megengedett kifejezésdomainből
vetít vissza. Nem használ SMT-t, tanúértéket vagy példaspecifikus felismerést.

## Helyességi Invariáns

Egy kiválasztott `x` célhoz két lefedő halmazt épít, `A` és `B` jelöléssel.
Minden, a kiinduló domainekkel összeegyeztethető értékeléshez létezik
`a in A` és `b in B`, amelyre `expr = a*x+b`. Nem állítja, hogy minden
halmazbeli pár megvalósítható, vagy hogy az együttható és a maradék független.

- A célváltozónál `A={1}`, `B={0}`; másik cellánál `A={0}`, `B=Delta(cell)`.
- Összeadásnál, negálásnál és ismert skálázásnál a halmazműveletek lefedik
  az összes lehetséges együtthatót és maradékot.
- Szorzásnál az egyik részfa együtthatóhalmazának pontosan `{0}`-nak kell lennie.
  Így nem marad el `x*x` tag. A másik részfa együtthatóját és maradékát a
  célfüggetlen oldal teljes lefedő értékhalmazával szorozza.

Ha `expr in R`, és **minden** lehetséges `a` invertálható, a cél lefedő halmaza
`{(r-b)/a | r in R, b in B, a in A}`. Az invariáns miatt minden valódi
célérték szerepel ebben a halmazban. A korrelációk elhagyása többletjelölteket
engedhet meg, de valódi megoldást nem zár ki.

A testmodulust minden halmazműveletnél figyelembe veszi, és az osztáshoz
moduláris inverzt használ. Nem feltételez egészszámos aritmetikát vagy a
moduláris körbefordulás hiányát. Lehetséges nulla vagy nem invertálható
együtthatónál az egész célvetítést kihagyja, nem csak a problémás ágat.
Modulus nélkül kizárólag maradék nélküli egész osztást fogad el.

A meglévő engine metszi az eredményt az aktuális Deltával, és az egyelemű
lefedő halmazból a szokásos módon tanul pontos értéket és egyértelműséget.
Többértékű vetítés önmagában nem kerül W-be, nem igazol megvalósíthatóságot,
nemegyértelműséget vagy teljességet. A már teljes domaineket nem szűkíti újra.

## Erőforráskorlátok

Egy kifejezés legfeljebb 256 csomópontját és 64 célját vizsgálja.
A részhalmazműveletekben és a végső osztásokban a meglévő 256-os végesdomain-
és Descartes-szorzat-korlát érvényes. Egy hívás összes célja legfeljebb 4096
csomóponti és értékkombinációs munkaegységen osztozik.
Keret- vagy reprezentációs hiba esetén nem ad részlegesen felsorolt halmazt.
A korábban, teljesen kiszámított más célvetületek továbbra is helyesek.
Az eredeti domaineket és kényszereket ez a lépés nem módosítja.

## Ellenőrzés

A célzott tesztek változóazonosítóktól és alkalmazási konstansoktól független
maradékos egyenleteket, halmazértékű együtthatókat, lookup-visszavetítést,
előjeles testelemeket, nulla és nem invertálható együtthatókat, ismétlődő
változókat, ismeretlen operandusokat és erőforráskorlátokat vizsgálnak.
Az 5, 7 és 11 elemű testeken több kifejezéscsalád minden megengedett
értékadását ellenőrzik: minden kielégítő értékadásnak meg kell maradnia minden
levezetett domainben. Ez regressziós ellenőrzés, nem a Rust-implementáció
géppel ellenőrzött formális bizonyítása.

A teljes soros release-készlet 519 sikeres, 0 hibás és 13 szándékosan kihagyott
teszttel zárult. Az all-targets fordítási és formázási ellenőrzés is sikeres.

## Invoice Release-kontroll

A standard konfiguráció és a kapcsolások módosítása nélkül végzett egyszeri
futások (3000 ms/hívás, 256 szemantikai próba, 160 szűkítési és 64 felderítési hívás):

| Változat | API-idő | SMT-hívás | Pontos cél | Többértékű domain | Teljes domain |
| --- | --- | --- | --- | --- | --- |
| Alap invoice | 0,70 s | 7 | 16 | 3 | 19 |
| H=21 jóváhagyás | 3,29 s | 16 | 17 | 4 | 21 |
| H=25 díjkatalógus | 27,12 s | 26 | 9 | 12 | 21 |

A harmadik változat második UCP-fázisa már levezeti a 0 kedvezménymaradékot
és a 10-es kedvezményszázalékot, ezért nincs 99 külön maradékjelölt-vizsgálat.
Az első SMT-fázis 12 hívás és 9,12 s, a második 14 hívás és 14,36 s lett.
A 12 valóban többértelmű célt továbbra is nem egyedinek igazolja, és az összes
riportált domain egyezik a teszt független egészszámos referenciájával.
A korábban beküldött napló ugyanilyen kiírt konfigurációval 136 hívást és
263,65 s teljes időt jelzett. Ez egyszeri futások összevetése, nem statisztikai
sebességmérés vagy általános gyorsulási garancia. Külön utólagos SMT-validációt
ezek a recovery-tesztek nem futtatnak.
