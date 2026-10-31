# Számlaaudit Jóváhagyáshoz Kötött Felárral

**Egységes standard profil:** az alap invoice, a H=21 bővítés és a H=25
kontroll ugyanabból a konfigurációból indul. Fast probe, domainszűkítés és
domainfelderítés egyaránt engedélyezett; az ütemező az aktuális tudás alapján
választ. A `combined` a standard kompatibilis neve, a `refinement` külön
komponensmérési kontroll. Az alábbi időadatok történeti futások, nem az új
alapbeállítás új mérései.

**Korábbi refinement-mérés:** a [teljes modellminták megosztásával](shared-model-samples.md)
a H=21 változat egyszeri release-próbája 2,43 s és 16 hívás, mind a 21 cél-domain
teljes. A fázisonkénti SMT-hívásszám 1, 9 és 6; az első jelöltkizárás után
változatlanul új UCP-fázis következik, 12 további pontos célértékkel.
Az alábbi korábbi mérések még a lefedést újraellenőrző verziók eredményei.

Ez a dolgozati számlapélda külön, összefüggő változata. Az eredeti
`InvoiceAudit<ALL>` kapcsolás megmarad összehasonlítási alapnak; a bővített
`InvoiceAudit<ALL, true>` ugyanazokat a termék-, kupon-, adó-, szállítási és
beszállítói szabályokat használja. Az elemző működő kódja és heurisztikája nem
változik a példa kedvéért.

Források:
- [Kapcsolás](../korrekt/src/circuit_analyzer/ucp/thesis_examples/invoice_circuit.rs)
- [Teszt és független referencia](../korrekt/src/circuit_analyzer/ucp/thesis_examples/invoice_approval_tests.rs)
- [Az eredeti számla részletei](../korrekt/src/circuit_analyzer/ucp/thesis_examples/README.md)

## Feladat És Kényszerek

A vállalati számlán kézi felár is szerepelhet, de csak kivételes jóváhagyással.
A jóváhagyási mód privát kategória, a felár privát összeg:

```text
r in {0,1,...,9}
0 <= a < 65536
a * (r - 5) = 0
G = E + V + S + a
H = 10*r - r*r
```

A módot egy kategórialookup, a felárat négy hexadecimális számjegy korlátozza.
A jóváhagyás külön sorban szerepel; a számlakapu pozitív rotációval éri el a
felárat. A `H` publikus auditérték kitalált üzleti összesítő, nem kriptográfiai hash.
A kapcsolás a kifejtett `r*r - 10*r + H = 0` polinomot tartalmazza,
nem a levezetett gyöklistát vagy az `a=0` egyenletet.

A megfigyelések:

```text
N = 124, W = 71600, P = 352, G = 208148, H = 21
```

A teljes rendszer szerint `r` csak 3 vagy 7 lehet, ezért `r-5` nem nulla,
és a szorzatkényszerből `a=0`. Ettől a végösszeg ismét korlátozza az eredeti
kosarat: `(q1,q2,q3,q4)=(37,29,25,33)`.
A két jóváhagyási mód, két kuponosztály és hat beszállítói pár 24 különböző
privát bemeneti kombinációt enged. A kosár tehát visszaállítható anélkül, hogy
a teljes tanú egyértelmű lenne.

## Tényleges Visszacsatolás

Az önálló UCP fixpontjában az öt ismert célérték a szállítási osztály és díj,
valamint a három fuvarozói könyvelési összeg. A termékmennyiségek 55 elemű
lefedő domainekre szűkülnek, de nem válnak pontossá. A mód domainje még
`{0,...,9}`, a felárnak nincs explicit véges domainje.

Az általános premisszavezérelt ütemező a szorzatkényszerből felismeri, hogy
az 5 kizárása hasznos lehet. Az első SMT-művelet ellenőrzi a lefedést, majd
kizárja az 5-öt. Ekkor rögtön visszatér az UCP-hez a kilencelemű
`{0,1,2,3,4,6,7,8,9}` lefedő domainnel. Sem a mód pontos értékét, sem annak
végleges `{3,7}` domainjét nem szükséges előbb meghatározni.

A következő valódi UCP-fázis visszaállítja `a=0` értékét, majd a négy
termékmennyiséget és a hozzájuk tartozó számlaértékeket. A 21 célból ekkor
17 pontos érték és négy többértékű domain ismert. A mód további ellenőrzése
az új pontos tényekkel folytatódik; a végső domainek:

```text
coupon_c in {2,3}
supplier_u in {4,10,16,22,28,34}
supplier_v in {3,9,15,21,27,33}
approval_mode_r in {3,7}
```

A teljes teszt nem csupán a végső számokat ellenőrzi: a fázisnaplóban külön
megköveteli az 5 pontos értékes UCP-t, az újraindítást kérő SMT-domainszűkítést,
majd a 17 pontos értékes UCP-t. A kosarat és a felárat ebben a második UCP-ben
kell visszaállítani. A heurisztika szimulációi nem számítanak valódi UCP-fázisnak.

A példa a jelenlegi szabályok kifejezésfelismerési határát is mutatja.
Ha később az UCP az általános kifejtett kvadratikus polinomokat is megoldja,
korábban is visszaállíthatja az adatokat; ez képességjavulás, nem helyességi hiba.
Nem indokolt ilyen fejlesztést letiltani a demonstráció fenntartásáért.

## Valódi Többértelmű Kontroll

`H=25` esetén `r=5` megengedett, így a felár ténylegesen elfedhet eltérő kosarakat.
Az összes többi publikus megfigyelést változatlanul hagyva például:

| Kosár | Felár | Jóváhagyási mód |
| --- | ---: | ---: |
| `(37,29,25,33)` | 0 | 5 |
| `(38,28,26,32)` | 432 | 5 |

Mindkét tanút ugyanazokkal az instance értékekkel ellenőrzi a MockProver.
Külön UCP-kontroll vizsgálja, hogy a visszaállítás nem zárja ki a referencia
szerint valóban lehetséges kosarakat vagy felárakat. Ez nem a teljes protokoll
adatvédelmi bizonyítéka, hanem egy konkrét többértelműségi kontroll.

A `thesis_invoice_approval_control_recovery` teszt ugyanezt a H=25 változatot
a teljes UCP--SMT recovery API-val is elemzi. A H=21 teszttel közös futtatósegéd
biztosítja az azonos profilt, kereteket, célcellákat és névvel ellátott fázisnaplót.
A referencia minden közölt domaint lefedésre, minden teljességi és egyediségi
állítást helyességre ellenőriz. A négy termékmennyiség és a felár egyikét sem
jelentheti pontosnak vagy egyedinek. Az erőforráskorlátos, részleges eredmény
megengedett; ez nem a teljes adatvédelmi védelem igazolása.

Az első teljes `refinement` release-próbában (3000 ms/hívás, 48 szűkítési hívás)
az UCP 1,09 s alatt öt pontos célt adott. Az első SMT-fázis 11 hívással, 3,13 s
alatt igazolta az `r=5` pontos értéket. A második UCP 1,02 s alatt nem talált
új céltényt. A második SMT-fázis 37 hívása 99,14 s alatt nem szűkítette tovább
a célok domainjeit; timeoutok után elfogyott a globális szűkítési keret.
A teljes API-idő 106,00 s lett: 6 pontos érték, 11 többértékű domain, 6 teljes
domain, 15 ismeretlen egyértelműségű cél, `QueryLimitReached` eredmény.
Ebben a profilban a recovery nem igazolta SMT-vel a kosár nemegyértelműségét;
annak bizonyítékát a külön ellenőrzött alternatív értékadások adják. Ez egyszeri,
korlátos futás, nem medián és nem a kontroll teljes megoldáshalmazának felsorolása.

## Díjkatalógusos Kontroll

**Új keresési változat:** a [kis domaineket is újrahasználó SMT-keresés](domain-assisted-search.md)
ugyanazzal a 3 s/hívás és 48 hívásos kerettel 88,92 s alatt futott le, és a kupon
nemegyértelműségét is igazolta. Továbbra is részleges eredmény maradt.
Az alábbi 104,46 s és 5,85 s mérések az ezt megelőző, csak pontos tényeket
újrahasználó változathoz tartoznak.

A dolgozati harmadik változatként külön vizsgálható szűkebb kontroll megtartja
a `H=25` megfigyelést és a teljes számlafolyamatot, de egy új lookup
`a in {0,432}` feltételt ír elő. Ez felármentes vagy fix díjas szolgáltatásként
értelmezhető. A széles, 16 bites feláras kontroll nem változik és nem törlődik.
Az új típus `InvoiceAudit<ALL,true,true>`; csak ebben konfigurálja és tölti fel
a külön díjkatalógust. A régi típusok nem kapnak új lookupot vagy táblát.

Az egészszámos referencia pontosan két kosarat enged: `(37,29,25,33)` felár 0-val,
illetve `(38,28,26,32)` felár 432-vel. Két kuponkategória és rendre hat, illetve
hét beszállítói pár mellett ez 26 különböző privát bemeneti kombináció.
A referencia-/MockProver-teszt mind a 26-ot azonos publikus értékekkel ellenőrzi,
és egy, kizárólag az új díjkatalógust sértő számlát elutasíttat.
A recovery ugyanazt a futtatósegédet, 21 célcellát és kereteket használja;
a referenciaeredményeket nem adja át premisszaként az elemzőnek.

Az első `refinement` release-próba az alapértelmezett 3000 ms/hívás és 48 hívás
mellett 104,46 s lett. Az első UCP 0,58 s alatt 6 pontos célt és 15 többértékű
domaint adott. Az első SMT-fázis 14 hívással, 9,15 s alatt `r=5`-öt állapított
meg; az új UCP 0,87 s alatt nyolc domaint szűkített, köztük mind a négy
termékmennyiséget a két valódi jelöltre. A második SMT-fázis 34 hívása 93,09 s
alatt nem hozott további céltényt. A végállapot `QueryLimitReached`: 7 pontos
érték, 14 többértékű domain, 7 teljes domain és 14 ismeretlen egyértelműségű cél.
Az elemző ebben a futásban nem bizonyította SMT-vel a többértékű célok
nemegyértelműségét vagy teljességét. Ezek referenciaeredmények, nem a recovery
által kiadott bizonyítványok. A katalógus javította a propagációs domainszűkítést,
de a teljes SMT-ellenőrzést az alapkerettel nem tette gyorsan befejezhetővé.
Ez egyszeri futás, nem ismételt benchmark.

Külön 100 ms/hívásos próbában ugyanazok a kosárvetületek 5,85 s alatt
előálltak, szintén 48 hívás és részleges végállapot mellett. A recovery-teszt
kifejezetten elvárja a négy mennyiség és a felár referenciával egyező szűk
domainjét, nem pusztán azt, hogy ne jelentsen téves pontos értéket. A rövid
kerethez tartozó idő nem a teljes domainigazolás ideje.

## Futtatás És Mérés

Az aktuális, [kis domainekkel is segített keresés](domain-assisted-search.md)
H=21 `refinement` release-próbája 2,90 s és 28 hívás lett, mind a 21 domain
teljességének igazolásával. A következő 4,11 s mérés az előző verzióhoz tartozik.

A korábbi, csak pontos tényekkel segített lefedés egyszeri `refinement` release-próbája
4,11 s és 28 solverhívás lett, az alapértelmezett 3000 ms/hívás kerettel.
Az első két hívás továbbra is kizárja az 5-öt, az UCP ezután 12 új pontos
értéket vezet le. A vizsgálat most az összes, 21 cél-domain teljességét igazolja:
17 pontos érték, négy teljes többértékű domain és négy bizonyítottan nem egyedi cél.
A több sikeres hívás a korábban timeout miatt elmaradt jelöltvizsgálatokat végzi el.
Ez nem ismételt benchmark, és nem hasonlítható közvetlenül a korábbi debugidőkhöz.

A korábbi [premisszavezérelt ütemezés mérése](premise-guided-refinement.md),
amelyben a lefedés még nem használta az igazolt pontos tényeket,
azonos keretekkel 27,66 s és 14 solverhívás lett; közvetlenül előtte a régi
ütemező 69,56 s és 27 hívás volt. A `combined` profil új futása 26,30 s,
19 hívás. Mindkettő a független referenciával egyező 17 pontos értéket és
négy többértékű domaint adott. Ezek egyszeri futások, nem statisztikai átlagok.

A referencia, a MockProver és a két solvermentes UCP-kontroll:

```bash
cargo test --offline -p korrekt --lib thesis_invoice_approval -- --nocapture --test-threads=1
```

A tényleges UCP--SMT--UCP visszaállítás, alapértelmezésben teljes standard profillal:

```bash
cargo test --offline -p korrekt --lib thesis_invoice_approval_recovery_feedback -- --ignored --nocapture --test-threads=1
```

A harmadik, többértelmű változat teljes recovery-futása release módban:

```bash
cargo test --release -p korrekt --lib thesis_invoice_approval_control_recovery -- --ignored --nocapture --test-threads=1
```

Ez is fogadja az `UCP_INVOICE_TIMEOUT_MS` hívásonkénti időkeretet (ms), valamint
az `UCP_INVOICE_APPROVAL_PROFILE=standard` (vagy `combined`) teljes profilt,
illetve a `refinement` kontrollprofilt. Külön
utólagos SMT-validációt nem futtat; a referenciaellenőrzés a teszt része,
nem a recovery API mért ideje.

A díjkatalógusos változat kapcsolásának és referenciájának ellenőrzése:

```bash
cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_reference_and_mock_prover -- --nocapture --test-threads=1
```

A díjkatalógusos változat teljes recovery-futása:

```bash
cargo test --release -p korrekt --lib thesis_invoice_surcharge_catalog_recovery -- --ignored --nocapture --test-threads=1
```

Ugyanazokat az `UCP_INVOICE_TIMEOUT_MS` és `UCP_INVOICE_APPROVAL_PROFILE`
beállításokat használja, mint a többi jóváhagyásos változat.

A `combined` profil ugyanaz a teljes konfiguráció, mint az alapértelmezett `standard`:

```bash
UCP_INVOICE_APPROVAL_PROFILE=combined cargo test --offline -p korrekt --lib thesis_invoice_approval_recovery_feedback -- --ignored --nocapture --test-threads=1
```

Az egységes alapkeret 256 szemantikai próba, 160 domainszűkítési solverhívás,
64 domainfelderítési solverhívás, legfeljebb 128 szűkítési jelölt/cella,
16 felderítési minta/cella, 32 egység köztes munkakeret és 3000 ms/hívás.
A `refinement` kontroll ebből a szemantikai és felderítési keretet tiltja le.
A köztes munkakeret
szemantikai próbákat és domainellenőrzési solverhívásokat számol, nem minden
esetben egyezik a tényleges solverfolyamatok számával. A standard szemantikai
újrapróbálkozása célonként legfeljebb egy, új tudáshoz kötött folytatást enged;
nem ad automatikusan hosszabb időkeretet. Az időkeretet az
`UCP_INVOICE_TIMEOUT_MS`, a kereteket az `UCP_INVOICE_SEMANTIC_QUERIES`,
`UCP_INVOICE_REFINEMENT_CHECKS` és `UCP_INVOICE_DISCOVERY_CHECKS` változó állítja.
A profilok nem adnak előre cellasorrendet,
gyököket vagy visszaállított értékeket a rendszernek.

### Korábbi Ütemező Mérései

Az alábbi mérések a premisszavezérelt korai átadás előtti állapothoz tartoznak.
A kapcsolás és az erőforráskeretek változatlanok maradtak.

Az első `combined` mérés 100,48 s, 35 solverhívás volt: UCP1 9,20 s,
SMT1 57,28 s/30 hívás, UCP2 3,98 s, SMT2 9,14 s/5 hívás, egyéb előkészítés
és ütemezés 20,89 s. A kezdeti létezést ellenőrzött tanú igazolta, nulla
SMT-hívással. Az első nyolc gyorspróba timeoutot adott; nem ezek állították
vissza a kosarat. Ez egyetlen minta, nem átlag vagy általános gyorsulási állítás.

Az akkor alapértelmezett `refinement` profil külön mérése:

| Fázis | Idő | Solverhívások | Eredmény |
| --- | ---: | ---: | --- |
| UCP1 | 9,37 s | 0 | 5 pontos érték, 12 nem egyelemű domain |
| SMT1 | 33,18 s | 22 | `r in {3,7}`, új propagáció szükséges |
| UCP2 | 4,02 s | 0 | 17 pontos érték, 4 nem egyelemű domain |
| SMT2 | 9,14 s | 5 | A mód két értékét megvalósíthatónak igazolja |
| Egyéb előkészítés és ütemezés | 11,70 s | 0 | Nem külön következtetési fázis |
| Összesen | 67,41 s | 27 | Ugyanazok a végső cél-domain-tartalmak |

Az SMT1 először a kedvezményszázalékot, majd a kupont ellenőrizte,
előrelépés nélkül. A mód 11 ellenőrzésből szűkült: egy lefedés- és tíz
jelöltellenőrzésből. A két megmaradó jelölt SAT-ellenőrzése ekkor még timeoutos
volt; a mód teljessége csak a második UCP utáni két SAT-válasszal igazolódott.
A három másik végső többértékű domain tartalma megfelelt a referenciának,
de teljesnek tanúsításuk a lefedésellenőrzések timeoutja miatt elmaradt.
Ez a mérés is egyetlen futás; a két profil összehasonlítása nem általános
SMT-hívásszám- vagy futásidő-garancia.

A `QueryLimitReached` státusz mellett is lehet mind a 17 helyes pontos érték
és négy helyes domain a riportban. Ez nem jelenti minden megmaradt domain
teljességének SMT-igazolását. A timeoutokat és bizonyítatlan teljességet a napló
külön feltünteti; azok nem adatvédelmi eredmények.
A korábbi mérések végállapotában a szemantikai gyorspróbák nulla, illetve nyolc próbás
kerete zárja le a további lehetőségeket, nem a 48 hívásos szűkítési keret
kimerülése. A három bizonytalan többértékű célnál a timeoutos lefedésellenőrzés
után változatlan tudásállapotban nincs újabb megengedett szűkítés.

A független egészszámos referencia mind a 21 cél vetületét ellenőrzi.
Egyetlen referenciaérték vagy privát tanúcella sem lesz elemzési premissza.
Az SMT-t használó tesztek sorosan futtatandók a közös kimeneti fájlok miatt.

Az új ütemezővel ellenőrzött könyvtári regresszió 492 sikeres, 0 hibás és 11 szándékosan
kihagyott teszttel zárult. Az itt dokumentált teljes SMT-visszaállítást külön,
az ignored teszt explicit indításával is ellenőrizte a mérés.
