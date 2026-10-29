# Relational UCP Propagation

General relational rules strengthen the existing equation/domain fixpoint. None
uses circuit names, cell indices, application-specific constants, witness
assignments, or solver queries.

## Lineáris Elimináció És Intervallumos Következtetés

A `linear_domains.rs` az alulhatározott lineáris rendszer hasznos következményeit
is felhasználja, nem csak a teljes rangú részrendszerek konkrét megoldását.
A kezdeti pontos értékek behelyettesítése után sorok lineáris kombinációit képzi.
A soroknak nem kell minden változót meghatározniuk. A ritkábban szereplő
segédcellákat előbb eliminálja; a sorrend heurisztika, nem helyességi feltétel.
A generált sorok a kezdeti premisszák következményei, ezért ugyanazon futás
feltételes ágaiban is érvényesek. Az eredeti kényszerek és az SMT-kontextus nem
változnak, az eredeti kifejezések riportált darabszáma sem nő.

A rendszer a cellák kanonikus `0..p-1` reprezentánsaihoz ideiglenes egész
intervallumokat rendel. A véges Delta-halmazok minimuma és maximuma adja a
kezdeti korlátot; domain nélkül a teljes testet veszi alapul. Így például egy
számjegyes összegből nagy csomagolt érték intervalluma is következhet anélkül,
hogy az egymillió lehetséges értéket Deltában felsorolná.

Egy `sum(a_i*x_i)+c = 0 (mod p)` sor bal oldalának intervallumából meghatározza,
hány `k*p` többszörös jöhet szóba. Ha egy sem, ellentmondást igazol. Ha pontosan
egy, az adott egész egyenletből szűkíti az operandusok intervallumát. Ha több,
ezzel a lépéssel nem szűkít: nem feltételezi indokolatlanul a körbefordulás
hiányát. A negatív együtthatókat, valamint a lefelé és felfelé kerekített egész
osztást külön kezeli. A sorok közös tényezőjével csak akkor oszt, ha az
modulo `p` invertálható.

Az eredeti és a levezetett soroknál véges támogatottsági vizsgálatot is végez.
Egy invertálható együtthatójú cellát kiválaszt, a többi cella teljes véges
Descartes-szorzatát bejárja, és minden kombinációnál kiszámítja a kiválasztott
cella egyetlen testbeli értékét. A már igazolt domainekkel és intervallumokkal
összeegyeztethető sorértékadások vetületei lefedő domainek. Ezek nem feltétlenül
elégítik ki a teljes circuitet, ezért nem kerülnek W-be, és nem igazolják a
többértékű domain teljességét. A meglévő domainek egészszám-reprezentánsait
megtartja, hogy egy `-1` és `p-1` közötti alakváltás ne okozzon hibás metszést.

Az új lépés korlátai:

| Keret | Jelentés |
| --- | --- |
| 256 bemeneti lineáris sor | Ezen felül nem generál új összefüggést; az eredeti engine továbbra is feldolgozza az összes kényszert |
| 128 eliminációs oszlop | Nagyobb rendszernél kihagyja a sorok kombinálását; a kiválasztott eredeti sorok korlátait továbbra is vizsgálja |
| 16 intervallumkör | Korai megállásnál az addig igazolt külső közelítést tartja meg |
| 4096 kombináció soronként | Csak teljes bejárás esetén ad támogatottsági vetületet |
| 16384 kombináció hívásonként | Kimerüléskor a további sorvizsgálatot kihagyja, nem zár ki meg nem vizsgált jelölteket |
| 256 tárolt domainérték | Változatlan reprezentációs korlát; túl nagy halmazból nem tanul csonkított Deltát |

A normál engine-fixpont az új domaineket is visszacsatolja a többi szabályhoz.
Az intervallumok átmenetiek, nem új nyilvános domainváltozatok. A módszer nem
teljes lineáris-egész vagy polinomiális megoldó, és a rendezés a korlátok mellett
befolyásolhatja a következtetés erejét, de a megtartott értékek helyességét nem.

A közvetlen regressziók kimerítő kis moduláris értékadásokat, több összekapcsolt
sort, átnevezett cellákat, megfordított sorrendet, negatív együtthatókat,
mezőbeli aliasokat, nem invertálható együtthatókat és a kombinációs keret
kimerülését vizsgálják. A kerekítési teszt nagy, számjegyekkel korlátozott
értékre következtet teljes tartomány-enumeráció nélkül.

Az egyszerű árus példában a `2*x+y+z=A` és `3*x+2*y+2*z=B` egyenletekből
most már az UCP is levezeti `x=2*A-B` értékét, akkor is, ha `y` és `z` nem
egyedi. A korábbi dolgozatszöveg azon állítása, hogy ezt csak az SMT találja
meg, ezért az új implementációra már nem érvényes. Az SMT utáni új UCP-fázist
a külön settlement-audit példa továbbra is ténylegesen demonstrálja.

## Finite Tuple Memberships

`UcpLookup` stores a bounded relation of full tuples rather than independent
column domains. A tuple is discarded only when an input's current covering
domain excludes its corresponding value. Projections of the remaining tuples
then give new covering domains for the input expressions. Existing affine
inverse propagation transfers these restrictions to cells.

Every satisfying assignment must choose a table row compatible with all its
input domains. Filtering incompatible rows therefore preserves all satisfying
assignments. Unknown or unrepresentable expression domains do not exclude rows.
Field aliases are normalized before comparison. A projected multi-value domain
is not automatically a complete feasible projection.

The Halo2 extractor retains correlations for supported unrotated fixed table
columns. Input rotations, selectors, and fixed constants use the existing
cell-level conversion. Relations exceeding 256 distinct rows or 16 columns,
and partially unknown/poisoned rows, are omitted in their entirety. Existing
safe unary projections and the original SMT lookup encoding remain available;
the relation is never truncated to fit.

## Finite Radix Candidate Filtering

The existing base-conversion recognizer identifies equations of the form
`x = d0 + b*d1 + ... + b^n*dn`. The new rule requires a recorded finite domain
for `x`, valid digit domains within `0..b-1`, and the existing no-wrap condition.
Thus each candidate for `x` has at most one integer digit representation.

For each inspected candidate, the engine creates a hypothetical copy of the
knowledge and supplies that value and its uniquely decoded digits. Ordinary
UCP and tuple propagation may then refute it through a nonzero zero-equation,
disjoint covering domains, or a tuple membership with no compatible row.
Only a refuted candidate is removed from the original packed domain. No other
hypothetical values, uniqueness facts, or completeness certificates are merged.

This is a bounded failed-candidate inference, not a satisfying-model enumerator.
A surviving candidate need not be feasible, so it is not added to W. Only the
remaining covering domain, and uniqueness if it becomes singleton, are learned.

Candidate filtering permits at most 256 candidate probes per UCP invocation and
16 ordinary propagation rounds per conditional probe. Probes do not recurse.
Unvisited candidates and inconclusive probes are retained. These generic effort
limits do not change the 256-value storage bound. A fixpoint remains relative
to implemented rules and effort/representation limits, not all consequences.

Already complete packed domains are not narrowed. Hypothetical copies discard
multi-value completeness certificates, because an additional assumption can
restrict a previously complete marginal projection. Scheduling simulations use
ordinary tuple/equation propagation without nested candidate probes, bounding
the cost of heuristic scoring separately from real knowledge propagation.

## Regression Evidence

`relational_propagation_tests.rs` checks tuple correlations, affine inputs, field
aliases, rotated extraction, inactive rows, oversized-table fallback, and exact
small-field projections. Radix tests use several bases, moduli and digit counts;
they also cover cell renaming, equation reordering, modular wraparound, isolation
of hypotheses, unsupported constraints, and both effort-limit boundaries.

The existing correlated-lookup refinement test now needs three SMT checks
instead of five: two impossible candidates are eliminated before refinement.
The risk-audit kernel now obtains the reference four-element score domain with
four publications, and the exact score with all five. Its constraints and
private witness policy are unchanged. No general quadratic factorizer was added;
the unseeded expanded calibration equation still needs SMT discovery.

These regression checks are not a formal proof of the Rust implementation.
