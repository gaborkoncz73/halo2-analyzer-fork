# Forraskodhoz kotott UCP-bizonyitas Aeneasszal

Ez a csomag a tenyleges Rust-forrast forditja Charon es Aeneas segitsegevel
Leanre, majd a generalt fuggvenyekre bizonyit matematikai helyesseget.
A `rust/lib.rs` `#[path]` moduljai kozvetlenul a `korrekt/src` fajljait
hasznaljak. Nincs kulon verifikacios Rust-masolat, `cfg`-vel helyettesitett
fuggvenytorzs vagy konkret circuitre szabott felteves. A recovery fociklusa
az eles futasban es a kinyeresben is ugyanaz a `recovery_loop.rs` modul.

## Mi van bizonyitva?

Az egyertelmusegi szabalyok ket eles belepopontja:

- `rules.rs::expression_is_unique`: ha `true` az eredmenye es K tenyei
  helyesek, a kifejezes minden kielegito ertekadasban ugyanazt az erteket adja.
- `rules.rs::infer_assigned_cell_from_zero_equation_with_modulus`: ha
  visszaad egy cellat, es a bemeneti kifejezes valoban nulla minden
  megoldasban, akkor az a cella egyertelmu. A modulus a modellezett test
  karakterisztikaja, es nagyobb egynel.

A fo tetelek: `SourceProof.rust_uniqueness_sound` es
`SourceProof.rust_assign_sound`. Ezek kozvetlenul a generalt Rust-fuggvenyek
eredmenyet veszik premisszanak, nem csupan egy fuggetlen modellre vonatkoznak.

A konkret `facts.rs::mark_unique` es `mark_initial_unique` metodusokat is
kinyeri. A `Proofs/KnowledgeUpdate.lean` bizonyitja az igazolt cella
bejegyzesenek invariansmegorzeset, a valodi elorelepest jelzo visszateresi
erteket, a tobbi cella valtozatlansagat, es az Assign--K-frissites lancot.
Az inicializalo metodus az advice cellat nem veszi fel bizonyitek nelkul.

### A domainallapot konkret kodja

A `Proofs/DomainState.lean` a `value.rs` valtozatlanul kinyert
`known_value`, `exact_value`, `is_singleton`, `domain_is_complete`,
`for_hypothetical_reasoning` es `bounded_value` fuggvenyeit ellenorzi.

- `rust_known_value_is_forced`: lefedo domainek es SAT mellett a
  visszaadott ertek minden eredeti megoldasban kotelezo.
- `rust_complete_domain_matches`: hianyzo domain nem complete;
  az Exact alaktag automatikusan, a FiniteSet csak explicit jelolessel complete.
- `rust_complete_domain_is_exact`: a lefedesi es a tarolt jelolesek
  helyessegi invariansa mellett a complete domain pontosan a megvalosithato ertekhalmaz.
- `rust_hypothetical_preserves_covering`: erosebb kontextusban a
  masolt domainek tovabbra is lefedok, az explicit teljessegi jelolesek uresednek.
- `rust_bounded_value_never_truncates`: a sikeresen megtartott ertek
  az eredeti egesz, legfeljebb 4096 biten. A nagyobb ertek elutasitasa
  nem jelent csonkolast vagy modularis atirast.

A szemantika az egesz reprezentansokat kulon ertelmezesi fuggvennyel
kapcsolja a testelemekhez. Nem koveteli meg, hogy ket kulonbozo egesz
kulonbozo testelemet jeloljon. A teljessegi jelolesek helyessege meg
premissza: a `try_mark_complete_from_samples` teljes szemantikai bizonyitasa nincs kesz.
A lekerdezes bizonyitasa nem bizonyitja
automatikusan a jelolest eloallito kodot.

### Veges halmazepites es domainbeolvasztas

A `Proofs/FiniteDomains.lean` a forrasbol generalt `finite_set` ciklust
ellenorzi. Az invarians szerint az osszegyujtott es a meg hatralevo
ertekek unioja a teljes bemenet. A `some domain` eredmeny pontosan ezt a
halmazt jeloli; a `none` megengedett elutasitas, nem egy reszleges prefix
elfogadasa. A tetel a veges iterator bejarasi szerzodese mellett
terminaciot es panikmentesseget is igazol, csokkeno hatralevo elemszammal.
Nem allitja, hogy minden nem ures, tamogatott bemenetbol feltetlenul some
lesz. A konkret BTreeSet-bejaras es a klonozo metszet-iterator modelljeire
a bejarasi szerzodest is ellenorzi.

A `rust_intersection_sound` a generalt `intersect` osszes enum-agat
ellenorzi. A `Proofs/DomainMerge.lean` a tenyleges `mark_domain` kodra
bizonyitja a lefedes es a tarolt teljessegi igazolasok megorzeset, a tobbi
cella valtozatlansagat, a complete domain modosithatatlansagat, es azt,
hogy false visszateresnel nincs rejtett allapotvaltozas.
A `mergeDomainTail` bizonyitasbeli reszkifejezes: a generalt fuggvennyel
valo kapcsolatat Lean definicios egyenloseggel ellenorzi, nem feltetelezi.

A metszes a tarolt egesz reprezentansokon tortenik. A beolvasztasi tetel
ezert `RepresentativeCover` invarianssal dolgozik: az osszehasonlitott
domainek ugyanazokkal a reprezentansokkal fedik le a megoldasokat.
Az uj `CanonicalMerge.lean` ezt modulo-lefedesi tetellel kapcsolja ossze:
kanonikus bemeneti domainekbol a konkret Rust-beolvasztas megorzi a
testelem-osztalyok lefedeset. A normalizalo hivashelyeknek tovabbra is
igazolniuk kell a bemeneti invarians fennallasat; a teljes adapter
ennek nem automatikusan kovetkezmenye. Tetszoleges modulo-aliasok
normalizalas nelkuli keveresere nincs igazolas.
A bitszamoknak u64-ben abrazolhatoknak kell lenniuk; ez nem a 4096 bites
tarolasi limit feltetelezese, a nagyobb ertek elutasitasa is ellenorzott.

### Konkret normalizalas es a teljessegjeloles magja

A `Proofs/FieldNormalization.lean` a kinyert `normalize_field_value`
fuggvenyre bizonyit megfelelest, sikeres normalizalast, maradekmegorzest,
aliasazonositast es idempotenciat. A modulusnak nagyobbnak kell lennie
egynel es a tamogatott 4096 bites korlaton belul kell maradnia.
A hibas es tul nagy modulus elutasitasa is ellenorzott. A Rust elojeles
osztasat `Int.tdiv`, maradekat `Int.tmod` modellezi, nem felcserelt
Euclidean osztas. Pozitiv modulus mellett a bizonyitas teremti meg
a kapcsolatot a matematikai `%` muvelettel.

A teljessegjeloles logikaja az eles `try_mark_complete_from_samples`
fuggvenybe kerult; a regi `mark_complete_from_samples` ezt hivja, es
csak a strukturalt hibaokot alakitja a korabbi anyhow-uzenette.
Az egyelemu vektort a vec! makro alacsony szintu muveletei helyett
Vec::new/push epiti. Nincs alternativ verifikacios algoritmus.
Az API/uzenetek es allapotfrissitesek azonossagat kulon Rust-regressziok
ellenorzik; a diagnosztikai wrapperre nincs formalis ekvivalenciatetel.

Az uj mag teljes torzse es ciklusa mar kinyert kod. A
`Proofs/CertificationControl.lean` a hianyzo domain agara, a
normalizalasi hiba valtozatlan taroloval torteno visszateresere es a
normalizalt kulccsal torteno jeloltbejegyzesre bizonyit konkret teteleket.
**Ez meg nem a teljes mag invariansmegorzese.** A mintak gyujtesenek,
a reszhalmaz/elemszam ellenorzesenek es a teljessegi jeloles irasanak
egyuttes kodszintu bizonyitasa tovabbra is nyitott.
A `normalized_sample_cardinality_certifies_complete` a kivant kriterium
szemantikai specifikacioja, nem e hianyzo kodkapcsolat helyettesitese.

### A recovery fociklusa

A `privacy.rs::recover_private_inputs` a `recovery_loop.rs::run_recovery`
generikus fociklust hivja. Az adapter a korabbi muveleteket hajtja vegre,
a fociklus pedig a propagacio, keresesi tenyek frissitese, muveletvalasztas,
kereses es beolvasztas sorrendjet donti el. A `propagate_until_stable`
kulon fuggveny, igy nincs az Aeneas altal nem tamogatott beagyazott
ciklusvezerles. A refaktoralt valtozat es a korabbi verzio kozott nincs
kulon formalis ekvivalenciabizonyitas; a viselkedest regresszios tesztek ellenorzik.

Az Aeneas a tenyleges ket ciklust es a hibaagakat generalja. A
`Proofs/RecoveryLoop.lean` ezeken bizonyitja, hogy a muveletek szerzodesei
mellett a sikeres visszateres megorzi az allapotinvarianst, a keresesi
allapot keszen all, es a leallasi feltetel ervenyes. A bizonyitas nem
korlatos cikluskifejtes, hanem a generalt ciklus fixpontjanak indukcioja.

- `rust_propagation_returns_ready`: a stabilizalas utan friss keresesi allapotot ad.
- `rust_recovery_success_is_sound`: a sikeresen visszatero eles fociklus megorzi az invarianst.
- `rust_recovery_preserves_knowledge`: ugyanez a K/Delta/W/E es a non-unique
  allitasok szemantikai invariansara instancialva.
- `rust_recovery_exact_value_is_forced`: a sikeres vegallapot singletonjanak
  erteke minden eredeti megoldasban kotelezo, a dokumentalt szerzodesek mellett.

A `Proofs/RecoveryControl.lean` szerzodesektol fuggetlenul is ellenorzi a
generalt torzsek konkret vezerleset: a kapott query-eredmeny a megfelelo
merge-hivasba kerul, es a query/merge/propagacio hibaaga nem valik sikerre.

**Ez modularis, reszleges helyessegbizonyitas.** Nem bizonyit feltetlen
terminaciot, es a konkret `RecoveryDriver` ot szerzodesenek implementacios
bizonyitasa meg hianyzik. A szerzodesek explicit tetelpremisszak, nem
feltetelezett axiomak vagy `sorry`-val kitoltott bizonyitasok. A pontos
nyitott kotelezettsegeket a [CONTRACTS.md](CONTRACTS.md) sorolja fel.

A bizonyitas az osszes veges kifejezesfara, tetszoleges melysegre es
korlatlan matematikai egeszekre ervenyes. Nem kis bemeneti tartomany
enumeralasa. A specifikacionak valo egyezes a generalt fuggveny sikeres
visszatereset is igazolja az alkalmazott Aeneas-szemantikaban; fizikai
memoria- vagy veremkimerulesre nem ad garanciat.

A lefedett esetek: Var, Const, Neg, Add, Mul, Scale, mind a negy
`UcpScalar`-valtozat, a rekurziv Assign-jeloltkereses, jeloltek osszevonasa,
cella-klonozas, nulla- es nemnullasag-felismeres. Az ismeretlen konstansok
erteke elofordulasonkent kulonbozhet; csak a witness megvalasztasatol
fuggetlenek. Az Assign-tetel a modulusos belepopontra vonatkozik, nem allit
testbeli helyesseget a modulus nelkuli egeszszamos nemnullasagi tesztrol.

Az `Audit.lean` minden `SourceProof`-tetel tranzitiv axiomafuggosegeit
ellenorzi. Csak `propext`, `Classical.choice` es `Quot.sound` megengedett;
`sorry`, sajat axioma es `native_decide`-fuggo bizonyitas nem.

## A bizonyitas pontos hatara

Ez **felteteles, forraskodhoz kotott funkcionalis verifikacio**, nem a
teljes analyzer, a compiler vagy a fuggosegek teljes bizonyitasa.

| Reteg | Bizonyitasi statusz |
| --- | --- |
| A ket belepopont es a bizonyitasban hasznalt sajat segedfuggvenyek | Generalt kod, ellenorzott megfelelesi es soundness-tetelek. A puszta kinyeres nem bizonyit minden generalt definiciot. |
| `num-bigint` | Az `Int`-reprezentacio, konverzio, egyenloseg, rendezes, `Int.tmod`, `Int.tdiv`, osszeadas/kivonas, ertekazonos clone es bits kulso konyvtari modell. A crate implementacioja nincs bizonyitva. |
| `HashSet`, `HashMap`, `BTreeSet`, `Borrow` | Extenzionalis tagsagi/bejegyzesi/lekerdezesi es ertekazonos klonozasi modell; a BTreeSet veges Finset. A fa, allocator es hasheles implementacioja nincs bizonyitva. |
| BTreeSet-bejaras es Iterator::map | Teljes veges bejaras es a hivasok kozott tovabbadott iterator/closure allapot modellje. A bejaras konkret rendezett sorrendjet nem modellezi; a bizonyitott domainmuveletek a sorrendtol fuggetlenek. |
| BTreeMap, Iterator::all/collect es Result-gyujtes | A `CollectionModels.lean` explicit tagsagi es bejarasi modelljei; a collect az elso Err-nel megall, az all megorzi a closure belso allapotat a hivasok kozott. A valodi standard konyvtari implementacio es a mag teljessegi hivasgrafjanak helyessege ettol meg nincs bizonyitva. |
| Hasherek modelljei | Csak a tagsagi API tipusfuggosegeit elegitik ki; nem jelentenek igazolt hash-implementaciot. A tagsagi modell nem futtatja oket. |
| Halo2 -> UCP kinyeres | A konstansok es az AST helyes ertelmezese premissza. A frontend husege nincs bizonyitva. |
| `recovery_loop.rs` ket ciklusa | A generalt kod modularis, reszleges helyessege bizonyitott. |
| Konkret `RecoveryDriver`, solver, K/Delta/W/E frissites | A konkret muveleti szerzodesek bizonyitasa meg hianyzik. A generikus fociklus bizonyitasa nem igazolja automatikusan az adaptert. |
| Kezdeti SAT, inicializalas, vegso riportszerializalas | A generikus cikluson kivul maradnak; nincs rajuk teljes forraskodhoz kotott bizonyitas. |
| Rust -> MIR -> Charon -> Aeneas, Lean kernel | Megbizhato eszkozlanc, nem e projekt altal bizonyitott forditok. |

A kulso konyvtari modellek a `TypesExternal.lean` es `FunsExternal.lean`
fajlokban explicit definiciok, nem uj axiomak. Ettol meg a Rust-konyvtarakkal
valo megfelelesuk elfogadott szerzodes marad, nem bizonyitott implementacio.
Az axiomamentes Lean-audit **nem** bizonyitja e kulso modellek Rust-huseget.
A HashMap-lekerdezes konkret hivasai az identitas-Borrow-t hasznaljak;
a konyvtari modell helyes Eq/Hash/Borrow es ertekazonos Clone szemantikaval
ertendo. A BigInt `bits` modellje a nagysag bitjeit szamolja, elojeltol
fuggetlenul. Ha maga a bitszam sem ferne u64-be, a korlatlan Int-modell
hibat ad; erre a fizikailag nem tarolhato meretre nincs Rust-megfelelesi allitas.

## Futtatas

A repo gyokerebol, Linux x86_64 alatt:

```bash
bash korrekt/verification/aeneas/bootstrap.sh
bash korrekt/verification/aeneas/verify.sh
```

A bootstrap rogzitett, SHA-256-tal ellenorzott Aeneas es Lean binarisokat
tolt le a gitbol kizart `.tools/` ala, valamint telepiti a szukseges Rust
nightlyt `rustup`-pal. A fuggosegek elso letoltese es a build-cache tobb GB
tarhelyet igenyelhet. A korabbi Lean 4.24.0 modellprojektet nem modositja:
az Aeneas-backend kulon Lean 4.35.0 csomag.

A `verify.sh` mindig ujra kinyeri az eles Rust-forrast, ujrageneralja a
Lean-kodot, majd osszehasonlitja a rogzitett kodot, LLBC-t es forrashasheket.
Elavult kinyeresnel hibaval leall, nem csak a regi Lean-fajlokat epiti ujra.
A koztes JSON osszehasonlitasakor csak a Charon ideiglenes kimeneti utjat
hagyja figyelmen kivul; az Aeneas mindig a valtozatlan Charon-kimenetet olvassa.
A forras szandekos modositasa utan:

```bash
bash korrekt/verification/aeneas/verify.sh --update
```

Ez frissiti a generalt eredmenyt, de utana ugyanugy kotelezo a bizonyitasok
sikeres ellenorzese. A generalt `Types.lean` es `Funs.lean` fajlokban kezzel
nem szabad algoritmust modositani.

A pinned Aeneas-kodgeneralas egy nevutkozese miatt a script az `Option.none`
es `Option.some` konstruktorok puszta neveit teljes nevukre minositi.
Ez reprodukalhato, szintaktikai utomunka; nem valtoztat elagazast,
fuggvenyhivast vagy visszateresi erteket. A modulaliasok ugyancsak csak az
`expr`/`cell` helyi valtozonevek es modulnevek utkozeset kerulik el.
Tovabba a Rust-tipusok Lean-univerzumat `Type 0`-ra rogziti: a pinned backend
a generikus `Result` hibaagakon kulonben nem old fel bizonyos
univerzumegyenleteket. Ez az univerzumpolimorfizmust szukiti, nem az
ertektartomanyt vagy a vezerlest. Az utomunka is a megbizhato eszkozlanc resze.

A kinyeres `-filter-trait-methods` opciot hasznal: a pinned backend
Iterator-modelljebol hianyzo map traitmezot kihagyja, a kozvetlen
map-hivast es a next muveletet viszont generalja es explicit konyvtari
modellel kapcsolja ossze. A Rust `cloned()` kifejezes helyett az azonos
ertekeket eloallito `map(|value| value.clone())` alak szerepel, mert a
cloned trait-alairasa frontend-hibat okoz. A runtime algoritmus valtozatlan.

A Rust-forrasok sajat egysegtesztjei onalloan is futtathatok:

```bash
cargo +nightly-2026-09-17 test --locked \
  --manifest-path korrekt/verification/aeneas/rust/Cargo.toml
```

A kis harness tesztmodjaban a domainmodul nem importalodik, mert annak
sajat tesztjei a teljes analyzer engine-tol fuggenek. A Charon nem
tesztmodban mindig az eredeti domainmodult forditja, nem masik torzset.
A domainek Rust-regresszioit az eles crate-ben kell futtatni:

```bash
cargo test --locked -p korrekt --lib ucp::value::completeness_tests
```

## Rogzitett eszkozok

- Aeneas: `nightly-2026.10.31-ab34bd2`, commit
  `ab34bd28458a08c150b7cbf1873e59af74588138`.
- Charon: `0.1.304`, commit `7b462d9159db2ed3015162352183906a30bfafc6`.
- Rust: `nightly-2026-09-17`, minimal profil, `rustc-dev` es `rust-src`.
- Lean es Mathlib: `4.35.0`; a tovabbi Lean-reviziokat a manifest rogziti.
- `num-bigint`: `0.4.6`; a Rust-grafot a `rust/Cargo.lock` rogziti,
  az eles workspace megfelelo verzioival.
- `anyhow`: `1.0.102`, a domainmodul tipusellenorzesehez;
  a kivalasztott logikai belepopontok nem hivnak anyhow-muveletet.

Hivatalos dokumentacio: <https://github.com/AeneasVerif/aeneas>.
