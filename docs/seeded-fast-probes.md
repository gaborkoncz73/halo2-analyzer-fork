# Fast Probe Igazolt Kezdőmintával

A recovery fast-probe stratégiája ugyanazt az eredeti SMT-pillanatképet és
ugyanazokat az igazolt keresési tényeket használja, mint a jelöltenkénti
refinement. Ezt a működést a `shared-model-seeded-probes-v9` szabályzat vezette be;
a jelenlegi [standard konfiguráció](unified-private-recovery.md#standard-and-ablation-configurations)
`standard-all-searches-v10` néven minden keresési komponenst engedélyez.
A régi `Analyzer::query_ucp_cell_uniqueness_with_value` API és a QED2 jellegű
alulkényszerezettségi útvonal változatlan marad.

## Működés

- Ha W(v) már tartalmaz megvalósítható értéket, a probe abból indul, nem kér
  új kezdő modellt. Két különböző minta mellett az ütemező eleve kihagyja.
- Minta hiányában teljes SAT-modellt keres. A vizsgált cella mellett a még
  nem teljes célok modellértékeit is megőrzi W számára.
- Ezután a Gamma AND v != a kérdést teszi fel. Az a érték forrása kizárólag
  azonos eredeti kontextusban bizonyított W-minta vagy az előző SAT-modell.
  A Delta egy tetszőleges jelöltje nem helyettesítheti a megvalósíthatósági mintát.
- UNSAT esetén az érték pontos és egyedi. SAT esetén a másik célérték
  nemegyértelműséget igazol; ugyanabból a modellből más célok mintái is átkerülnek.
- UNKNOWN/timeout esetén nem állít egyértelműséget. Egy korábbi sikeres első
  modell mintáit ettől még megtartja. Hibás modell vagy végrehajtási hiba nem
  válik bizonyítékká vagy puszta timeouttá.

Kezdőmintával rendszerint egy, nélküle legfeljebb két solverhívás történik.
A fast-probe szemantikai próbakerete továbbra is egy próbálkozást számol;
a fázisnapló külön mutatja a tényleges solverhívásokat. A refinement híváskeretét
ezek nem fogyasztják. Az újrapróbálkozás és az összkeretek nem nullázódnak.

## Helyességi Határ

A snapshot és a publikus megfigyelések változatlanok. Az exact értékeket és
a kis lefedő domaineket redundáns állításként használja, a refinement meglévő
méretkorlátaival és aliaskezelésével. A vizsgált cél saját domainjét nem
feltételezi a kizárás igazolásához. Nem használ privát teszttanút, hipotetikus
domaint vagy részhalmazos SAT-modellt kezdőmintaként.

A cellánkénti minták nem feltétlenül kombinálhatók tetszőleges közös tanúvá.
Egyetlen minta nem válik pontos értékké, több minta önmagában nem lefedő domain.
A minták és a puszta teljességi jelölések továbbra sem indítanak új UCP-kört.
A független riportvalidálás nem feltételezi a recovery állításait.

## Ellenőrzés

A célzott tesztek ellenőrzik az egyhívásos, valódi SAT-ból gyorsítótárazott
kezdőértéket; az alternatív teljes modell más célokhoz tartozó mintáit; az
első modell megőrzését bizonytalan kizárás után; valamint a hiányzó,
ellentmondó és az alternatívaként tiltott értéket visszaadó modellek elutasítását.
Egy külön fast-probe-only integrációs teszt két korrelált cél teljes domainjét
igazolja egyetlen próbával, refinement vagy discovery és új UCP-kör nélkül.

A régi háromparaméteres solverinjektálási tesztek kizárólag tesztfordításban
adapteren át ugyanazt a fő recovery-ciklust futtatják. Az éles belépési pont
közvetlenül a snapshot-alapú probe-ot használja.

A teljes soros release tesztkészlet 505 sikeres, 0 hibás és 13 szándékosan
kihagyott teszttel zárult. Az all-targets fordítási, formázási és diff
whitespace-ellenőrzések szintén sikeresek.

## Release-próbák

| Példa és profil | Korábbi hívások | Új hívások | Új API-idő | Teljes domainek |
| --- | ---: | ---: | ---: | ---: |
| Alap invoice, combined | 10 | 7 | 0,69 s | 19/19 |
| H=21 invoice, combined | nem mért | 16 | 2,62 s | 21/21 |
| H=25 díjkatalógusos invoice, combined | 139 | 138 | 261,86 s | 21/21 |

A H=21 és H=25 futásban a refinement kerete 160 hívás, a fast-probe kerete
nyolc próba, az időkorlát 3000 ms/hívás. Az alap invoice meglévő combined
beállításai változatlanok. Mindhárom teszt sikeres.

Az alap számlán az u első két SAT-modellje már v két értékét és a kupon egyik
értékét is igazolja. Emiatt v külön fast probe-ja elmarad, és a kuponhoz csak
egy további jelöltvizsgálat szükséges. A H=21 futásban a jóváhagyási mód és a
kupon probe-ja is egy-egy, korábbi modellmintából indított hívás.

A H=25 kontrollon a kupon ismert 2-es mintájából induló probe egyetlen
hívással megadja a 3-as alternatívát. A korábbi combined futás 264,57 s volt;
az új futás 138 hívásából 133 refinement és 5 fast-probe hívás. Négy probe
továbbra is timeoutol: az adóalap és adó kezdő modellkeresése, valamint a
kedvezményszázalék és kedvezménymaradék közvetlen kizárási kérdése. A maradék
99 jelöltvizsgálata ezért nem marad el. A végeredmény változatlan: 9 pontos
érték, 12 többértékű domain, mind a 21 teljes, 12 nem egyedi cél, 0 ismeretlen.
Ez a módosítás megszünteti a fölösleges kezdő modellkeresést ismert mintánál,
de nem garantálja, hogy az összetett kizárás a solvernek könnyű lesz.

Ezek egyszeri futások, nem ismételt benchmarkok; a kis időeltérésből nem
következik általános gyorsulási arány. Külön post-recovery SMT-validálás nem
része a megadott időknek.
