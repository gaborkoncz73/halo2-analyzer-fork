# Kis Lefedő Domainek Az SMT-keresésben

A v7 recovery a [már levezetett lefedést is újrahasználja](established-domain-refinement.md),
így nem indít előzetes lefedési kérdést. Az alábbi v6 mérési táblázat a domainexport
első változatának történeti eredménye, nem a v7-é.

A recovery a pontos értékek mellett az aktuális Delta kis lefedő domainjeit is
átadja a snapshotból indított lefedési, jelölt- és teljes domainfelderítési
kérdéseknek. Az új állapot neve `PrivateSearchFacts`; a keresési vezető minden
valódi propagációs előrelépés után `established_search_facts` segítségével frissíti.
A szemantikai gyorspróba korábbi domainexportja és az ütemezés változatlan.

## Helyességi Feltételek

- A domain az eredeti C és a konkrét P mellett már levezetett lefedő halmaz.
  Nem szükséges teljesnek lennie: lehetnek benne megvalósíthatatlan jelöltek.
- A vizsgált cella és a vele azonos SMT-névre képezett másolati aliasok domainjét
  kihagyja az extra premisszák közül, lefedési és jelöltkérdésekben egyaránt.
- A mezőbeli értékeket normalizálja, a másolt cellák halmazait metszi.
  Üres halmazt vagy ellentmondó másolati tényeket hibaként kezel.
- A modellminták W-ből nem válnak lefedő premisszává. A hipotetikus szimuláció
  nem írhat a valódi Delta-állapotba. K tagsága konkrét domain nélkül nem elég.
- Minden kérdés változatlan eredeti snapshotból, külön fájlban épül fel.
  A jelöltfeltevések nem halmozódnak, a snapshot és a szó szerinti célzott
  részhalmazok változatlanok maradnak.
- A független riportvalidátor nem kapja meg ezeket a premisszákat.
  Ez a gyorsítás nem a UCP-től független ellenőrzés: a recovery a támogatott
  következtetési szabályok és a Delta-invariáns helyességére támaszkodik.

## Korlátok

Egy exportált véges domain legfeljebb 16 nyers jelöltet tartalmazhat; a normalizálás
összevonhat mezőbeli aliasokat. A többértékű domainek együttesen legfeljebb
512 jelöltegyenlőséget adhatnak a kérdéshez. A rendszer kisebb halmazokat választ
először, azonos méretnél stabil SMT-név szerinti sorrendben. A túl nagy vagy a
keretbe nem férő halmazt egészben hagyja ki, nem csonkítja. A pontos értékek
korábbi, külön méretkorlát nélküli exportja megmarad. Ezek belső exportkorlátok,
nem módosítják a Deltát, a solver-timeoutot vagy a keresés híváskereteit.

## Ellenőrzött Mérési Eredmény

A díjkatalógusos invoice ugyanazzal a `refinement` profillal, release builddel,
3000 ms/hívással és 48 szűkítési hívással futott:

| Mutató | Csak pontos tényekkel, korábbi futás | Kis domainekkel is |
| --- | ---: | ---: |
| Teljes API-idő | 104,46 s | 88,92 s |
| Solverhívások | 48 | 48 |
| Pontos célértékek | 7 | 7 |
| Többértékű cél-domainek | 14 | 14 |
| Teljes cél-domainek | 7 | 7 |
| Bizonyítottan nem egyedi célok | 0 | 1 |
| Ismeretlen egyértelműségű célok | 14 | 13 |

Az új futás SAT-mintákat talált a kedvezményszázalékra és a kuponra, és
bizonyította a kupon nemegyértelműségét. A kedvezmény maradékának lefedő
domainjét 89 jelöltre szűkítette, ami új, érdemi céltény nélküli UCP-fázist indított.
A kosár kétértékű vetületei változatlanok maradtak. A vizsgálat továbbra is
`QueryLimitReached`, és számos lefedési kérdés timeoutolt: a gyorsítás nem oldotta
meg a teljes domainigazolást. Ezek egyszeri futások, nem mediánok és nem minden
circuitre érvényes gyorsulási garanciák.

Az alap invoice külön release-próbája 1,05 s és 16 hívás, a H=21 feláras
változaté 2,90 s és 28 hívás lett. Előbbinél mind a 19, utóbbinál mind a 21
cél-domain teljes maradt; a korábbi eredmények tartalma és a visszacsatolás
megmaradt. Ezek is egyszeri mérések, nem a régi benchmark JSON-ok új átlagai.

A teljes soros könyvtári regresszió 495 sikeres, 0 hibás és 13 szándékosan
kihagyott teszttel zárult. Az összes target fordításellenőrzése, a formázás és
a diff ellenőrzése is sikeres. A célzott tesztek lefedik az aliasokat,
normalizálást, teljesnek nem jelölt domaineket, exportkeretet, önfeltételezés
kizárását és az eredeti snapshot változatlanságát. Ez tesztlefedettség,
nem géppel ellenőrzött formális implementációbizonyítás.

Futtatás:

```bash
cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_recovery -- --ignored --nocapture --test-threads=1
```

Az új mérési szabályzatok: `domain-assisted-refine-discover-v6` és
`premise-guided-domain-assisted-refinement-v6`. A régi benchmarkfájlok történeti
adatok; az új változattal történő összehasonlításnál meg kell őrizni a beállításokat.
