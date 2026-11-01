# A privat visszaallitas verifikacioja

A dolgozat allitasainak es a teteleknek a megfeleltetese: [THESIS_CLAIMS.md](THESIS_CLAIMS.md).

Ket csomag talalhato itt, kozos Lean 4.35.0 eszkozlanccal:

- `Recovery/`: a kovetkeztetesi szabalyok es a tudasallapot matematikai modelljei.
- [`aeneas/`](aeneas/README.md): a valtozatlan Rust-forrasbol automatikusan kinyert
  kod bizonyitasai. Ez a csomag a `Recovery` modelleket is importalja, es a
  `core_refines_model` tetellel kapcsolja a kinyert allapothoz.

A `Recovery` modellek tetszoleges cella- es ertektipusra, illetve a reprezentacios
retegben tetszoleges egeszekre es pozitiv modulusra ervenyesek.

**A teljes Rust-forras nincs formalisan verifikalva.** A pontos implementacios hatart az
[IMPLEMENTATION_STATUS.md](IMPLEMENTATION_STATUS.md) tartalmazza.

## Futtatas es VS Code

A teljes ellenorzes a repo gyokerebol:

```bash
bash korrekt/verification/aeneas/bootstrap.sh
bash korrekt/verification/aeneas/verify.sh
```

Csak a modellcsomag a rogzitett eszkozzel:

```bash
cd korrekt/verification
PATH="$PWD/aeneas/.tools/lean/bin:$PATH" lake build
```

A VS Code **Lean 4** bovitmeny (`leanprover.lean4`) mutatja a bizonyitasi celt.
A modellcsomagnak nincs Mathlib-fuggosege; az Aeneas-csomag Mathlibet hasznal.
A `lake build` nem futtatja a Rust-teszteket. A generalasi eredmenyek a gitbol kizart
`.lake` mappaba kerulnek.

## Olvasasi sorrend

| Modul | Szerep |
| --- | --- |
| `Recovery/Semantics.lean` | Ertekadas, rogzitett kontextus, megvalosithatosag, lefedes, teljesseg, egyertelmuseg. |
| `Recovery/Domains.lean` | Metszes, mintamegorzes, singleton, teljesseg es redundans keresesi megszoritasok. |
| `Recovery/FiniteDomains.lean` | Listas veges domainek, korlatos lekepzes es Descartes-szorzat; nincs csonkitas. |
| `Recovery/ExpressionDomains.lean` | Az ismert konstansos kifejezesek AST-je, kiertekelese es domainkiertekelesenek indukcios bizonyitasa. |
| `Recovery/Algebra.lean` | Kommutativ gyurutulajdonsagok es az affin egyenlet igazolt inverzzel valo megoldasa. |
| `Recovery/FieldReasoning.lean` | Nullosztomentesseg, nulla/differencia es nemnulla tenyezovel valo egyszerusites. |
| `Recovery/Uniqueness.lean` | Var/Const/Op/Zero kifejezes-egyertelmuseg es az Assign stabil maradekos esete. |
| `Recovery/AffineProjection.lean` | Minden egyutthatot ellenorzo inverzalas, affin vetites es biztonsagos domainbeolvasztas. |
| `Recovery/AffineSplit.lean` | A rekurziv affin felbontas es a teljes felbontas-vetites lanc bizonyitasa. |
| `Recovery/Normalization.lean` | Elojelhelyes maradekjavitas, kanonikus reprezentans, bitkorlat es muveleti kongruencia. |
| `Recovery/CanonicalDomains.lean` | Normalizalt, deduplikalt domainek; modulo lefedes es mintak; teljesseg reszhalmazbol es elemszambol. |
| `Recovery/Root.lean` | A faktorizalt Root-szabaly, a nemnulla skalazas es az affin vetitessel valo osszekapcsolas. |
| `Recovery/AllButOne.lean` | All-But-One egyertelmuseg, konkret ertekek es az indexgyokok modulo-kulonbozosege. |
| `Recovery/BaseConversion.lean` | Helyiertekes kodolas, dekodolas, no-wrap, egyertelmuseg es veges packed domainek vetitese. |
| `Recovery/Knowledge.lean` | Egy cella opcionalis domainje, mintai, explicit teljessegi jelolese es allapotmuveletei. |
| `Recovery/Execution.lean` | Lepesenkenti es tetszoleges veges vegrehajtasra vonatkozo invariansmegorzes. |
| `Recovery/GlobalKnowledge.lean` | Tobbcelles K/Delta/W/E, eredmenybeolvasztas, modellek megosztasa es riportallitások. |
| `Recovery/GlobalExecution.lean` | A teljes modellezett veges vegrehajtas es riport felteteles soundness-tetele; kumulativ solverhivasok. |
| `Recovery/ContextReasoning.lean` | Redundans keresesi premisszak, reszhalmazos kizarasok es hipotetikus kontextusvaltas. |
| `Recovery/ConditionalReasoning.lean` | Lefedo selector-domain osszes aganak unioja es a bizonytalan ag helyes fallbackje. |
| `Recovery/Cache.lean` | A domainkiertekeles valtozofuggosegei es a cache-hit helyessege. |
| `Recovery/PropagationView.lean` | A K/Delta-nezet es a mintak/teljessegi metadatok kulonbsege; felteteles fixpont-atvitel. |
| `Recovery/SolverSteps.lean` | Az SMT-lepesek szemantikai bizonyitasi kotelezettsegei. |
| `Recovery/Checks.lean` | A feltetelek szuksegesseget szemlelteto, geppel ellenorzott ellenpeldak. |
| `Recovery/PropagationChecks.lean` | Ket elemu test, konkret visszaallitas, korrelacio, nulla egyutthato, nem affin szorzat es elemszamkorlat. |
| `Recovery/RepresentationChecks.lean` | Negativ maradek, azonos testelemek, bitkorlat, elemszam-feltetel es 255 bites reprezentans. |
| `Recovery/RuleChecks.lean` | Root/Assign/All-But-One/Base-Conv alkalmazasok es a feltetelek elhagyasanak ellenpeldai. |
| `Recovery/Lookup.lean` | Rendezett n-esek szurese, oszlopvetites, korrelacio, ures tabla kielegithetetlensege. |
| `Recovery/GlobalChecks.lean` | Teljes tobbcellas modellfutas, korrelalt mintak, kontextuscsere, subset-SAT es cache-invalidation. |
| `Recovery/Audit.lean` | A Recovery-tetelek tranzitiv axiomafuggosegeinek automatikus ellenorzese. |

## A bizonyitott allitasok

Az `Feasible ctx cell` az eredeti, publikus megfigyelesekkel rogzitett
`ctx` kontextus kielegito ertekadasaibol szarmazo ertekek halmaza.
Az egesz modellezett vegrehajtas alatt ugyanaz a kontextus marad ervenyben.

Az egycellas invarians harom resze:

- Minden rogzitett domain lefedi az osszes megvalosithato erteket.
- Minden megorzott mintahoz letezik az eredeti kontextust kielegito ertekadas.
- Igaz explicit teljessegi jelolesnel a rogzitett domain pontosan a
  megvalosithato ertekhalmaz.

A globalis invarians ezen felul a kontextus kielegithetoseget, a K es
non-unique cimkek helyesseget es a keresesi premisszak entailmentjet is megkoveteli.

A 190 nevvel ellatott tetel tobbek kozott bizonyitja:

- Ket lefedo domain metszete tovabbra is lefedo, es kielegitheto kontextusban nem ures.
- Megvalosithato mintak unioja tovabbra is helyes mintahalmaz.
- Ha minden domainjelolthoz van megvalosithato minta, a domain teljes.
- Kielegitheto kontextusban az egyelemes lefedo domain teljes es egyertelmu.
- Ket kulonbozo megvalosithato minta kizarja az egyertelmuseget.
- Egy teljes domain helyes uj lefedessel valo metszese nem valtoztat az ertekeken.
- Igazolt lefedo domain keresesi feltetelkent valo hozzaadasa redundans.
- Kizarasi UNSAT-bol lefedes, jelolt-UNSAT-bol biztonsagos torles kovetkezik.
- Discovery eseten a mintak es a vegso kizarasi bizonyitas egyutt teljes domaint adnak.
- Fast probe eseten megvalosithato minta es kizarasi UNSAT egyutt pontos visszaallitast ad.
- Az absztrakt allapotmuveletek barmely veges sorozata megorzi az invariansokat.
- A listas kifejezes-domainkiertekeles eredmenye minden tenyleges erteket tartalmaz,
  akkor is, ha a reszfak valtozoi korrelaltak.
- Sikeres korlatos muveletnel a teljes eredmenylista marad meg; tul nagy
  eredmenynel None keletkezik, nem egy csonkitott lefedo domain.
- Az affin egyenlet kommutativ gyuruben igazolt egyutthatoinverzzel helyesen megoldhato.
- Az affin felbontas osszeadasa, negalasa, skalazasa es megengedett szorzasa
  megorzi a valodi egyutthato-maradek parok lefedeset.
- A rekurziv `splitAffine` minden sikeres eredmenye helyes affin felbontas.
- Ha barmely lehetseges egyutthato inverze hianyzik, a vetites egeszet kihagyja.
- Az affin felbontas es a vetites egyutt lefedo domaint eredmenyez, amely
  az invarians megsertese nelkul a korabbi domainbe olvaszthato.
- A null-egyenletes specialis eset ugyanezt a lefedest igazolja.
- A Rust-szeru negativ maradek javitasa ugyanazt a nemnegativ maradekot adja,
  mint az euklideszi maradekkepzes.
- A normalizalas megorzi a maradekosztalyt, idempotens, es azonos testelemeket
  azonos reprezentansra kepez; a pozitiv es negativ bemeneti reprezentalas nem szamit.
- Reprezentalhato pozitiv modulus eseten a normalizalt ertek belefer a modulus
  bitkorlatjaba, a bemeneti egesz tetszoleges nagysaga mellett is.
- A normalizalt reszhalmaz es azonos elemszam csak ismetlesmentes mintakra
  adja a szukseges halmazegyezest; ebbol a domain modulo teljessege kovetkezik.
- A kifejezes-egyertelmusegi Bool-ellenorzo ismert skalaros AST-n minden
  pozitiv valasza helyes; K-tagsagbol nem kovetkeztet konkret ertekre.
- Az Assign szabaly stabil maradek es nemnulla egyutthato mellett,
  nullosztomentes gyuruben egyertelmuseget igazol.
- A mar faktorizalt Root-kifejezes sikeres gyokdomainje lefedo; nulla
  skalaval nem tanul gyokdomaint. A gyokdomain tovabbi affin vetiteshez is hasznalhato.
- Az All-But-One szabaly kulonbozo testbeli gyokok, egyertelmu selector
  es stabil osszeg mellett minden agcellat egyertelmuen meghataroz.
- Ismert selector- es osszegertek mellett az aktiv ag az osszeget kapja,
  a tobbi nulla. A 0..n indexek modulo kulonbozoseget a darabszam <= modulus igazolja.
- A Base-Conv kodolas fix hosszon, helyes szamjegykorlatokkal injektiv;
  az ismetelt maradek/osztas visszaadja az eredeti szamjegyeket.
- A Rustban hasznalt `base^n * (highest_max + 1) < modulus` feltetel
  a tobbi szamjegy korlataival egyutt tenylegesen kizarja a korbefordulast.
- Egyertelmu packed ertekbol az egyenlet es a no-wrap feltetel mellett
  a szamjegyek is egyertelmuek. Veges packed lefedesbol helyes szamjegydomain vetitheto.
- A tobbcellas eredmenybeolvasztas megorzi a domain-, minta-, egyertelmusegi
  es keresesi invariansokat, beleertve egy teljes modell tobb cellara megorzott mintait.
- A singletonokbol frissitett E es a kivalasztott lefedo domainek redundans
  solverpremisszak az eredeti kontextusban; puszta K-tagsagbol nem keletkezik konkret egyenloseg.
- A modellezett veges recovery vegeredmenyenek unique/non-unique/domain/complete
  es exact allitasai helyesek, ha a megadott lepesszerzodesek teljesulnek.
- A solverhivas-szamlalo a modellezett lepesek soran nem csokken, es az epoch
  novelese nem nullazza. Ez nem usize-overflow- vagy budget-enforcement bizonyitas.
- A helyes hint-ekkel vegzett kizarasok az eredeti kontextusra is ervenyesek.
  Gyengitett reszhalmazos UNSAT atviheto, de subset-SAT onmagaban nem mintabizonyitek.
- A lefedo selector-domain minden agabol helyes domain-unio kepezheto;
  bizonytalan agnal az eredeti lefedes megtartasa biztonsagos.
- A tamogatott domainkiertekelo cache-talalata megegyezik az ujraszamitassal,
  ha a rogzitett kifejezes es parameterek mellett a fuggosegi szignatura egyezik.

A `recovery_from_empty_is_sound` az ures tudasallapotbol indulo,
`Execution` relacioval leirt veges lepesekre vonatkozik. Nem bizonyitja,
hogy a tenyleges Rust-pipeline minden lepese ilyen atmenet, es nem allit
terminalast vagy minden kovetkezmeny felfedezeset.

## A globalis recovery-tetel

A `global_recovery_reports_sound` mar nem egyetlen cellara, hanem az
`AnalysisState` teljes K/Delta/W/keresesi allapotara vonatkozik. Az
`exactSearchFacts` az E pontos egyenlosegeit irja le; a `coveringSearchFacts`
a kivalasztott tobberteku domainhint-eket. A `searchFacts` e ket reszt fogja ossze.

A fo tetel feltetelei:

1. Az eredeti kontextus kielegitheto.
2. A vegrehajtas az `AnalysisExecution` relacio szerinti veges lepesekbol all.
3. Minden uj `RecoveryEvidence` domainje lefedo, mintai teljes eredeti
   modellekbol szarmaznak, es egyertelmusegi cimkei igazoltak (`EvidenceSound`).
4. Teljessegjelolesnel az osszes jelolthoz van minta, vagy a domain singleton.
5. A kontextus valtozatlan; uj hipotetikus premisszanal kulon allapot es
   a gyengitett megfelelo bizonyitasok szuksegesek.

Az `EvidenceSound` nem uj axioma: a konkret szabaly- es SMT-tetelekbol kell
eloallitani. A tetel ugyanakkor nem bizonyitja, hogy a Rust-pipeline minden
aga tenylegesen teljesiti ezt a szerzodest. Kulonosen nem igazolja a meg nem
modellezett BigInt-Mul, parser es solverfrontend reszeket. Nem allitja a
terminalast, a heurisztika optimalitasat vagy a vizsgalat teljesseget.

A `GlobalChecks.lean` a teljes modellezett vegrehajtasi relaciot is hasznalja:
ket modell minden kivalasztott cellahoz mintat ad, ezekbol non-unique cimkek
keletkeznek, domain viszont nem keletkezik pusztan a mintakbol.

## Kontextus, felteteles agak es cache

A `hypothesis_analysis_sound` szukebb kontextusra megorzi a regi lefedest,
K-tenyeket es mar entailt keresesi hint-eket, de torli a regi W-mintakat,
explicit teljesseget es non-unique cimkeket. A tenyleges szimulacios kod
ilyen allapot-megfeleltetese tovabbra is kulon kotelezettseg.

A felteteles domain-unio minden selector-lehetoseghez helyes aglefedest ker.
Egy UNSAT ag ures lehet; egy bizonytalan vagy kihagyott ag nem hagyhato el
bizonyitek nelkul. Az agon beluli unique cimkek nem adnak automatikusan
globalis unique eredmenyt, mert kulonbozo agak kulonbozo erteket adhatnak.

A `Cache.lean` a tamogatott `expressionDomain` kiertekelo szignaturajat
igazolja, nem a teljes Rust `Memo::infer`/relacios cache implementaciojat.
A kifejezes, aritmetika/modulus es meretkorlat a tetelben rogzitett.
A kulcs a relevans domaineket es a complete flageket is tartalmazza.

A `PropagationView.lean` mas szerepu: megmutatja, hogy puszta minta-,
complete- vagy keresesi metadata frissites nem valtoztatja meg a K/Delta
nezetet. A fixpont atvitele csak olyan propagatorra bizonyitott, amely ezen
a nezeten keresztul mukodik. Nem bizonyitott meg, hogy a teljes Rust engine
complete-fuggo kovetkeztetesi kapui megfelelnek ennek vagy mas ekvivalens
megorzesi szerzodesnek. Ezert a cache-invalidation es a globalis ujrafuttatasi
feltetel helyessege nem mosodik ossze.

## Az affin bizonyitas feltetelei

A `split_then_project_sound` mar nem ker kesz affin felbontast igazolo
`AffineSound` feltetelt: azt a modellbeli rekurziv `splitAffine` sikeres
lefutasa es a helyes bemeneti domainek alapjan bizonyitja.
A kovetkezo, explicit feltetelek szuksegesek:

- A bemeneti celladomainek lefedok az eredeti kontextusban (`FactsCover`).
- A muveletek teljesitik a `CommutativeRingLaws` strukturaban felsorolt,
  szokasos kommutativ gyurutulajdonsagokat.
- Minden sikeresen visszaadott egyutthatoinverz valoban inverz (`inverseSound`).
- A kifejezes erteke a jobboldali domainbe esik az eredeti kontextus minden modelljeben.
- A korlatos affin felbontas es vetites is sikeresen ad eredmenyt.

Nem eleg pusztan nemnullanak nevezni az egyutthatot; a bizonyitas tenyleges
inverzt kovetel. A matematikai feltetelek kommutativ gyurure es reszleges
inverzmuveletre is ervenyesek, igy nem hasznaljak ki bizonyitatlanul a
modulus prim voltat. A gyurutulajdonsagok tetelparameterek, nem sajat
globalis axiomak. A `PropagationChecks.lean` ezeket a ket elemu test
konkret muveleteire is bizonyitja, de a termelesi BigInt-muveletekre meg nem.

A `zero_equation_projection_sound` a `rhs = {0}` esetre szol, a
`split_then_project_merge_sound` pedig a kapott domain allapotba olvasztasat
is igazolja. A bizonyitas nem alapitja meg az igy kapott domain teljesseget:
a korrelaciok elhagyasa tovabbi, megvalosithatatlan jelolteket is megengedhet.

## A tovabbi szabalyok feltetelei

A `NoZeroDivisors` kulon feltetel: az egyszeru `modulus > 1` ellenorzes
nem bizonyitja. Osszetett modulus mellett peldaul `3 * (3-1) = 0 mod 6`,
de a 3 sem 0, sem 1 modulo 6. Ezert a Root es All-But-One tetelek nem
alkalmazhatok tetszoleges modularis gyurure. A ket elemu testben ezt a
tulajdonsagot a `boolean_no_zero_divisors` bizonyitja; a Halo2-test konkret
Rust-megfeleltetese meg nincs igazolva.

A `unique_expression_sound` a tenyleges Bool-ellenorzo modelljet bizonyitja.
Az `assign_from_stable_remainder` az Assign algebrai magjat igazolja,
nem a teljes Rust `analyze_assign_candidate` parser/dispatcher minden agat.
A stabil maradek konkret ertekenek ismerete nem szukseges.

A Root-modell mar faktorizalt alakkal indul, es nem vegez altalanos
polinomfaktorizalast. A Rust linearizalo parserenek a kozos affin reszre
es az elojeles gyokeltolasokra vonatkozo megfeleltetese meg nyitott.

Az All-But-One modell kulonbozo gyokokre altalanosabb a Rust 0..n
mintajanal; az indexgyokok kulonbozosegenek matematikai meretfeltetele
kulon bizonyitott. A gyujto/parser es a konkret K/Delta frissites nem resze ennek.

A Base-Conv tetelek nemnegativ egesz/Nat szamjegyekre es rogzitett
szamjegyszamra szolnak. Az egesz packed ertek es a testbeli egyenlet kozott
explicit modulo-egyenlet es no-wrap feltetel szerepel. Az eredmeny nem
feltetelez hibasan fuggetlen szamjegyeket, es nem teszi teljesse a vetitett domaint.
A BigInt, az elojeles reprezentansbol kanonikus maradekra lepes es a
helyiertek-minta parserenek vegrehajtasi megfeleltetese meg nyitott.

Az uj `Covers` eredmenyek a `merge_domain_sound` es az `Execution.Step.merge`
premisszajakent hasznalhatok, ezert a korabbi allapotinvarians-bizonyitas
ujrafelhasznalhato. A globalis modellben mar szerepel K, de ez sem jelenti
automatikusan a konkret Rust K-tarolo frissitesenek bizonyitasat.

## A reprezentacios bizonyitas hatara

A `normalizeRepresentative` az elojeles maradek, negativ maradek javitasa es
a felso felintervallum eltolasanak matematikai sorrendjet koveti.
A `normalizeField` a `modulus > 1` es a bitkorlat ellenorzeseit is modellezi.
A `FitsBits limit value` jelentese `abs(value) < 2^limit`; ez a kivant
matematikai szerzodes, nem a `num_bigint::BigInt::bits` implementaciojanak bizonyitasa.

A `CanonicalDomains.lean` szandekosan modulo ekvivalenciaval dolgozik.
Tetszoleges egesz kontextusban peldaul `-1` es `16` nem ugyanaz az ertek;
csak modulo 17 jelolnek azonos testelemet. A reprezentacios tetelek nem
azonositanak egesz ertekadasokat indoklas nelkul. A normalizalt listak
sorrendjet nem hasznaljak ki, es a sikeres meretellenorzes nem csonkit.

A `complete_modulo_from_normalized_cardinality` a Rust
`mark_complete_from_samples` reszhalmaz- es elemszam-ellenorzesenek
matematikai felteteleit igazolja. A BTreeMap/BTreeSet muveletek es a Rust
hibautvonalak nem ennek a tetelnek a reszei.

## Kapcsolat a Rust-koddal

A kinyert allapotra a `core_refines_model` bizonyitott kapcsolatot ad. A tobbi sor
szemantikai tervezesi kapcsolat, nem bizonyitott Rust--Lean programfinomitas:

| Lean | Rust (`../src/circuit_analyzer/ucp/`) |
| --- | --- |
| `intersect_preserves_coverage`, `merge_domain_sound` | `value.rs`: `intersect`, `mark_domain` |
| `remember_samples_sound`, `model_sample_is_sound` | `privacy_search.rs`: `remember_feasible_samples`; a teljes modellek mintainak megorzese |
| `complete_from_samples`, `certify_complete_from_samples_sound` | `value.rs`: `mark_complete_from_samples`; `privacy_search.rs`: `certify_complete_domains` |
| `singleton_cover_is_complete` | `value.rs`: `domain_is_complete` singleton-esete |
| `two_samples_prove_non_unique` | `privacy_search.rs`: `non_unique_cells` |
| `covering_hint_is_redundant` | `privacy.rs`: `smt_query_value_facts`; a kikovetkeztetett domainek solveres ujrafelhasznalasa |
| `SolverSteps.lean` | `privacy.rs`, `privacy_domain.rs`, `privacy_discovery.rs`: bizonyitott keresesi eredmenyek szemantikaja |
| `boundedMap`, `boundedCombine`, `expression_domain_sound` | `value.rs`: `map_domain_values`, `combine_domain_values`, `expression_domain_with_optional_modulus` tamogatott esetei |
| `CommutativeRingLaws.solve_affine` | `value_inference.rs`: `solve_linear_value` inverz alapu testbeli aga |
| `splitAffine`, `split_affine_sound` | `finite_projection.rs`: `Projection::split`, `scale`, `combine` |
| `projectAffine`, `split_then_project_sound` | `finite_projection.rs`: `Projection::project` |
| `normalizeRepresentative`, `normalizeField` | `value.rs`: `normalize_field_value`, `bounded_value` matematikai szerzodese |
| `canonical_finite_preserves_coverage` | `value.rs`: `finite_domain_from_values` normalizalo es deduplikalo szemantikaja |
| `complete_modulo_from_normalized_cardinality` | `value.rs`: `mark_complete_from_samples` normalizalt tartalmazas- es elemszamfeltetelei |
| `uniqueExpression`, `unique_expression_sound` | `rules.rs`: `expression_is_unique` ismert skalaros modellje |
| `assign_from_stable_remainder` | `rules.rs`: Assign algebrai kovetkeztetese; nem a teljes jeloltkereso parser |
| `rootCandidates`, `root_candidates_sound` | `value_inference.rs`: `infer_root_expression_domain` mar faktorizalt szemantikaja |
| `all_but_one_unique`, `all_but_one_exact` | `all_but_one.rs`: a megkovetelt szorzat- es osszegkenyszerek kovetkezmenyei |
| `highest_digit_bound_prevents_wrap`, `base_conversion_unique` | `base_conv.rs`: a no-wrap feltetel es a szamjegy-egyertelmuseg matematikai alapja |
| `unpack_packed_digits`, `failed_unpack_excludes_packing` | `base_conv.rs`: `exact_digits` nemnegativ, rogzitett hosszusagu modellje |
| `finite_base_projection_sound` | `base_conv.rs`: veges packed jeloltek szamjegy-vetitese; parser es allapotfrissites nelkul |
| `merge_evidence_sound`, `model_evidence_sound` | `privacy.rs`: `merge_established_results` es a `model_samples` megorzese |
| `refresh_search_facts_sound`, `hinted_exclusion_proves_original_coverage` | `privacy.rs`, `privacy_subset.rs`: E es domainhint-ek felhasznalasa a keresesi kerdesekben |
| `global_recovery_reports_sound` | `privacy.rs`, `privacy_report.rs`: a recovery es a riport szemantikai szerzodese |
| `conditional_domain_union_sound` | `engine.rs`: felteteles kovetkeztetesek agankenti lefedesenek unioja |
| `cached_expression_domain_sound` | `propagation_cache.rs`: a domain-kiertekeles cache-ujrafelhasznalasanak tamogatott esete |

## Bizonyitasi hatar es nyitott feladatok

- Az altalanos invariansok predikatumhalmazokat hasznalnak, a kifejezeses es
  affin reteg mar veges listakkal dolgozik. A reprezentacios reteg mar
  normalizal es deduplikal, de a `BTreeSet`/`BTreeMap` belso implementaciojat,
  a `BigInt` muveleteit es a Rust `bits()` szerzodeset nem bizonyitja.
- A listas meretkorlat az ismetleseket is szamolja, ezert konzervativabb
  lehet a Rust halmazos elemszamkorlatjanal. Az AST-, celcella- es teljes
  munkakeret-korlatok nincsenek modellezve; egyes modellbeli meretellenorzesek
  a lista felepitese utan tortennek. Futasi koltsegazonossagot nem bizonyit.
- A `Knowledge` egycellas modelljet mar az `AnalysisState` tobbcellas
  K/Delta/W/keresesi allapota egesziti ki. A konkret utemezo, jogosultsagi
  allapotgep, HashMap/HashSet tarolok es budget-enforcement meg nincsenek verifikalva.
- A modell explicit teljessegi flagje nem a Rust `domain_is_complete` teljes
  implementacioja. A singleton automatikus teljessegenek matematikai alapjat kulon tetel adja.
- A `Step.merge` uj domainjehez lefedesi, a `Step.remember` mintaihoz
  megvalosithatosagi bizonyitek szukseges. Ezek a konkret UCP- es keresesi
  implementacio bizonyitasi kotelezettsegei, nem mar igazolt implementacios tulajdonsagok.
- Az SMT-UNSAT valodi kielegithetetlensegi premissza. A cvc5 valaszat,
  az SMT-parsert es a Halo2-kodolas huseget a bizonyitas nem ellenorzi.
- Az ismert skalaros kifejezeses, affin, Root, All-But-One es Base-Conv
  modellek mar rendelkeznek a fent korulhatarolt bizonyitasokkal.
  A `UcpScalar::Unknown`/`NonZero`, a teljes `value_kind`/Assign elemzo,
  a modulus nelkuli egesz osztas es a tovabbi nemlinearizalo szabalyok,
  kulonosen a BigInt-Mul teljes algoritmusa meg nincsenek verifikalva.
- A szabalyok modellje es a Rust-kovetkeztetesi modulok megfeleltetese nincs bizonyitva.
- A szemantikai modell nem bizonyitja a Rust bemeneti adatfolyamat: a kezdeti
  privat witness csak letezest igazolhat, nem lehet recovery-mintak forrasa.
  A `modelEvidence` tenyleges SMT-modell eredetenek es a csak publikus
  recovery-premisszak hasznalatanak implementacios igazolasa kulon feladat.
- A forrashoz kotott bizonyitasok az `aeneas/` csomagban vannak.
- Uj hipotetikus premisszak mas kontextust jelentenek: regi teljessegi
  bizonyitasok nem vihetok at automatikusan. Erre a `Checks.lean` ellenpeldat tartalmaz.

## Bizonyitasellenorzes

A `Recovery.lean` gyokermodul az auditot is importalja, ezert a szokasos
`lake build` az axiomafuggosegeket is ellenorzi. A projekt a warningokat
hibakent kezeli. Az audit minden Recovery-tetelnel csak a standard
`propext`, `Classical.choice` es `Quot.sound` axiomakat engedi meg;
a `sorryAx`, egyedi axiomak es a compilerben bizva vegzett bizonyitasok
nem elfogadhatok. Sajat Recovery-axioma felvetele is hiba.

Az audit szamlaloja a generalt segedteteleket es nev nelkuli peldakat is
tartalmazza; nem a 190 kezzel elnevezett tetel szama. Az aktualis build
kiirja az ellenorzott deklaraciok szamat. A fo vegrehajtasi tetel es a
`complete_from_samples` egyaltalan nem fugg axiomatol; az uj affin es
kifejezeses tetelek csak a megengedett standard logikai axiomaktol fuggnek.

A dolgozatban vallalhato allitast a [THESIS_CLAIMS.md](THESIS_CLAIMS.md) rogziti.
