# A Rust-implementacio verifikacios allapota

## Mi van es mi nincs bizonyitva?

A `Recovery/` kezzel irt Lean-modelleket es azok geppel ellenorzott
teteleit tartalmazza. Az [`aeneas/`](aeneas/README.md) ezen felul ket
valodi Rust-belepopont automatikusan kinyert kodjara bizonyit soundnesst:
`expression_is_unique` es a modulusos Assign. A konyvtari modellek es a
kinyeresi eszkozlanc expliciten elfogadott fuggosegek.
Az eles `recovery_loop.rs` generalt fociklusara modularis, reszleges
helyessegbizonyitas is keszult. Ez meg nem a konkret `RecoveryDriver`
szerzodeseinek bizonyitasa; a nyitott reszeket az `aeneas/CONTRACTS.md` reszletezi.
**Egyetlen teljes Rust-modulrol vagy a teljes recoveryrol sem allitja,
hogy mar mindenestul verifikalt.** A tetelek darabszama nem
forraskod-lefedettseg es nem keszultsegi szazalek.

A celzott funkcionalis tulajdonsag: az elemzo helyes bemenet es explicit
megbizhatosagi feltetelek mellett nem kozol hamis egyertelmusegi, lefedesi,
megvalosithatosagi vagy teljessegi allitast. Ez mas feladat, mint minden
lehetseges Rust-hiba, teljesitmenyproblema es kulso fuggoseg igazolasa.
A teljesseg es az optimalis futasi sorrend nem soundness-kovetelmeny.

## Lefedettseg retegenkent

| Rust-reteg | Meglevo Lean-eredmeny | Hianyzo implementacios kapcsolat |
| --- | --- | --- |
| `value.rs`: halmazepites, metszes es beolvasztas | Aeneas: tenyleges finite_set-ciklus teljes-bemenet-megorzese es terminacioja, intersect minden enum-aga, mark_domain lefedes- es teljessegmegorzese, mas cellak es false-ag valtozatlansaga. | Konyvtari modellek Rust-husege, testbeli hivashelyek kozos reprezentans-invariansa, uj teljessegi jeloles eloallitasa. |
| `value.rs`: lekerdezes es hipotetikus masolat | Aeneas: konkret known_value, exact_value, is_singleton, domain_is_complete es for_hypothetical_reasoning. Lefedes/SAT mellett exact helyesseg; explicit jelolesinvarians mellett teljesseg; erositeskor lefedesmegorzes es jelolesek torlese. | A lefedesi es explicit teljessegi invariansokat eloallito irasi muveletek; konyvtari modellek Rust-husege. |
| `value.rs`: normalizalas es bitkorlat | Aeneas: konkret normalize_field_value megfelelese, maradekmegorzes, aliasok es idempotencia, moduluskorlatok; bounded_value csonkitasmentessege. Kanonikus bemeneti domainekkel a mark_domain modulo-lefedest is megoriz. | BigInt-konyvtari modell megfeleltetese; az eles hivashelyek kanonikus bemeneti invariansanak igazolasa. |
| `value.rs`: mintakbol teljesseg | Szemantikai normalizalt reszhalmaz/elemszam kriterium. Aeneas: az eles try_mark_complete_from_samples torzse/ciklusa kinyert; hianyzo domain, normalizalasi hiba es egy jelolt frissitesi lepese bizonyitott. | A teljes mintagyujtes es teljessegi allapotfrissites egyuttes kodszintu invariansa; diagnosztikai wrapper formalis ekvivalenciaja. |
| `value.rs`: kifejezesdomainek | Tamogatott AST-n korlatos domainkiertekeles. | UcpScalar-esetek, zero/nonzero gyorsitasok es Rust-rekurzio teljes kapcsolata. |
| `finite_projection.rs` | Rekurziv affin felbontas, vetites, kihagyas hianyzo inverznel, beolvasztas. | BigInt/extended-GCD, gyurutulajdonsagok konkret instancialasa, munkakeretek es celgyujtes. |
| `value_inference.rs`, `linear_domains.rs` | Affin megoldas es a faktorizalt Root matematikai modellje; Root + affin vetites. | A teljes dispatcher, linearis rendszerek, faktor/linearizalo parser es minden tovabbi szabalyag. |
| `rules.rs` | Aeneas: a tenyleges expression_is_unique es a modulusos Assign teljes rekurziv jeloltkeresese, minden UcpScalar-esettel, megfelelesi es soundness-tetelekkel. | Konyvtari modellek Rust-husege, frontend-kapcsolat, modulus nelkuli Assign testbeli ertelmezese es az engine allapotfrissitese. |
| `all_but_one.rs` | Kulonbozo gyokokkel egyertelmuseg es konkret ertekek; indexgyokok modulo-kulonbozosege. | A gyujto/parser, roots_for_sum es a konkret K/Delta frissites. |
| `base_conv.rs` | Fix hosszu kodolas/dekodolas, no-wrap, szamjegy-egyertelmuseg es veges packed domain vetitese. | BigInt, field--Nat megfeleles, helyiertek-parser, hibaagak es teljes Rust-finomitas. |
| `bigint_mul.rs` | Meg nincs kulon teljes modellszintu bizonyitas. | Limb-korlatok, carry-k, nulla tulcsordulas, algebra es Rust-finomitas. |
| `facts.rs`, `expr.rs`, `cell.rs` | Absztrakt szemantika; Aeneasbol konkret mark_unique/mark_initial_unique es Assign utani K-frissites. | Konyvtari modellek megfeleltetese, tovabbi adatszerkezet-muveletek es a teljes frontend-kapcsolat. |
| `engine.rs`, `propagation_cache.rs`, `pipeline.rs` | Felteteles aglefedések unioja, domaincache-szignatura, K/Delta-nezet, globalis allapotinvarians. | Teljes Rust-fixpont, inference/relacios cache, complete-fuggo kapuk es a tenyleges utemezes. |
| `privacy*.rs` keresesi es riportreteg | Tobbcelles K/Delta/W/E, eredmenybeolvasztas, modelmegosztas, hint/subset-kovetkeztetes, felteteles globalis riporttetel. | Konkret keresesi allapotgep es utemezes, eroforraskeretezes, HashMap/HashSet, scoped assertionok es Rust-riportlogika. |
| `recovery_loop.rs` | Az eles Rust-kodbol generalt ket ciklus modularis invariansmegorzese, frissesseg es sikeres kimenet. | A konkret RecoveryDriver szerzodeseinek es projekciojanak igazolasa; feltetlen terminacio. |
| `lookup*.rs`, `extractor.rs`, `plonkish.rs` | Meg nincs automatikus Rust-finomitas. | Halo2-kapuk, lookupok, masolatok es rotaciok husege. |
| `analyzer.rs`, `analyzable.rs`, SMT encoder/parser/process | Kulso kotelezettsegek a jelenlegi szemantikai tetelekhez. | A Halo2--SMT megfeleles, solvervalaszok ertelmezese, folyamat- es I/O-hibak. |
| Halo2, num-bigint, standard collections, cvc5 | A jelenlegi Rust-futas megbizhato fuggosegei, nem igazolt implementaciok. | Teljes bizonyitasuk kulon projektek vagy explicit elfogadott bizalmi hatar. |

Az osszefoglalo csoportositas nem allitja, hogy a fel nem sorolt
segedfajlok automatikusan bizonyitottak. A mintacircuitek es tesztek nem
helyettesitik a fenti implementacios kotelezettsegeket.

A `global_recovery_reports_sound` felteteles, tobbcellas szemantikai tetel:
SAT kontextusbol es szerzodeshelyes lepesek veges sorozatabol helyes
riportallitások kovetkeznek. A konkrét Rust-lepesek szerzodeshelyessege
es a kezdeti privat witness recovery-premisszakent valo felhasznalasanak
kizarasa meg nincs formalisan bizonyitva. Az eredet/provenance feltetel
kulonbozik attol, hogy egy minta matematikailag megvalosithato.

## A kozvetlen Rust-bizonyitas kovetkezo lepese

1. Rogziteni kell a bizonyitas pontos tulajdonsagait es bizalmi hatarat:
   sajat recovery/UCP-kod, frontend, standard konyvtar, BigInt es solver.
2. Az elso forraskodhoz kotott kinyeres es bizonyitas elkeszult az
   `aeneas/` csomagban a `rules.rs` ket belepopontjara. Ezt kell
   kiterjeszteni a domainmuveletekre es a recovery-allapotgep tovabbi reszeire.
3. A frontend, Rust-toolchain, Aeneas es Lean-backend verzioit egyutt kell
   rogziteni. Az Aeneas kulon Lean 4.35.0 csomagot hasznal; a regi
   Lean 4.24.0 tetelek nem kerulnek automatikusan at ebbe a bizonyitasba.
4. A kinyert kodon funkcioszerzodeseket es a meglevo modellel valo
   megfelelest kell bizonyitani, beleertve a panikot es hibautakat.
5. Minden kivul hagyott fuggvenyt es fuggoseget nev szerint kell jelezni.
   Az ismeretlen implementaciok feltetelezese vagy a hianyzo bizonyitas
   kitoltese axiomaval nem szamit az adott implementacio bizonyitasanak.
6. CI-ban a Rust-valtozas utan ujra kell futtatni a kinyerest es a
   bizonyitasokat, nem eleg a regi kezzel irt modellt ujraepiteni.

Az Aeneas hivatalos folyamatat es kulso definiciokra vonatkozo korlatait
az [Aeneas dokumentacioja](https://github.com/AeneasVerif/aeneas#usage)
irja le. A kinyeres a valtozatlan `cell.rs`, `expr.rs`, `facts.rs`,
`rules.rs`, `recovery_loop.rs` es a kivalasztott `value.rs` fuggvenyek
forrasait olvassa be, es ezek hivasgrafjat generalja. A matematikai normalizalasi tetelek ettol meg
nem valnak automatikusan implementacios bizonyitassa.

## A dolgozatban hasznalhato allitas

Bizonyitott: a leirt invariansok, az affin kovetkeztetes es a
reprezentacios muveletek megadott matematikai modelljei helyesek.
Tovabba az Aeneas altal kinyert ket UCP-belepopont implementacios
soundnesse, a dokumentalt konyvtari es szemantikai feltetelek mellett.

Meg nem bizonyitott: a teljes Rust-implementacio minden vegrehajtasa
megfelel ezeknek a modelleknek. A jelenlegi eredmenyt nem szabad
"formally verified Rust implementation" allitaskent bemutatni.
