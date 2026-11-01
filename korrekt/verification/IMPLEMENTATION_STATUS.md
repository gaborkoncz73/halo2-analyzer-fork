# A Rust-implementacio verifikacios allapota

## Mi van es mi nincs bizonyitva?

A `Recovery/` kezzel irt Lean-modelleket es azok geppel ellenorzott teteleit tartalmazza.
Az [`aeneas/`](aeneas/README.md) a valodi Rust-forrasbol kinyert kodra bizonyit: a
szabalyok ket belepontjara, a domainmuveletekre, a teljessegjelolesre, a recovery
beolvasztasi magjara es a fociklusra. A ket reszt a `core_refines_model` tetel kapcsolja ossze.

A fo tetel `rust_private_recovery_sound`. A szerzodesek a `coreMachine` gepre bizonyitottak.
A megmarado feltetelek explicit premisszak, a teljes listat a
[THESIS_CLAIMS.md](THESIS_CLAIMS.md) es az `aeneas/CONTRACTS.md` tartalmazza.
**A teljes Rust-implementaciorol nem allitja, hogy mindenestul verifikalt.**
A tetelek darabszama nem forraskod-lefedettseg es nem keszultsegi szazalek.

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
| `value.rs`: mintakbol teljesseg | Aeneas: az eles `try_mark_complete_from_samples` teljes torzsere es ciklusara `rust_certification_preserves_knowledge`. | A diagnosztikai wrapper formalis ekvivalenciaja; a konyvtari modellek Rust-husege. |
| `value.rs`: kifejezesdomainek | Tamogatott AST-n korlatos domainkiertekeles. | UcpScalar-esetek, zero/nonzero gyorsitasok es Rust-rekurzio teljes kapcsolata. |
| `finite_projection.rs` | Rekurziv affin felbontas, vetites, kihagyas hianyzo inverznel, beolvasztas. | BigInt/extended-GCD, gyurutulajdonsagok konkret instancialasa, munkakeretek es celgyujtes. |
| `value_inference.rs`, `linear_domains.rs` | Affin megoldas es a faktorizalt Root matematikai modellje; Root + affin vetites. | A teljes dispatcher, linearis rendszerek, faktor/linearizalo parser es minden tovabbi szabalyag. |
| `rules.rs` | Aeneas: a tenyleges expression_is_unique es a modulusos Assign teljes rekurziv jeloltkeresese, minden UcpScalar-esettel, megfelelesi es soundness-tetelekkel. | Konyvtari modellek Rust-husege, frontend-kapcsolat, modulus nelkuli Assign testbeli ertelmezese es az engine allapotfrissitese. |
| `all_but_one.rs` | Kulonbozo gyokokkel egyertelmuseg es konkret ertekek; indexgyokok modulo-kulonbozosege. | A gyujto/parser, roots_for_sum es a konkret K/Delta frissites. |
| `base_conv.rs` | Fix hosszu kodolas/dekodolas, no-wrap, szamjegy-egyertelmuseg es veges packed domain vetitese. | BigInt, field--Nat megfeleles, helyiertek-parser, hibaagak es teljes Rust-finomitas. |
| `bigint_mul.rs` | `linear_system_rule_evidence`: teljes oszloprangu rendszer megoldasa egyertelmu. | A Rust-linearizalo es `rank_mod` kod. |
| `facts.rs`, `expr.rs`, `cell.rs` | Aeneas: mark_unique, mark_initial_unique, Assign utani K-frissites. | Konyvtari modellek megfeleltetese, frontend-kapcsolat. |
| `engine.rs`, `propagation_cache.rs`, `pipeline.rs` | `engine_execution_sound`: tetszoleges veges `EngineStep`-sorozat megorzi a K/Delta invarianst; `qed2_fixpoint_soundness`. Felteteles aglefedesek, cache-szignatura modellben. | A `run_cached` kod es az `EngineStep` megfelelese; a vezerles nem kinyerheto. |
| `privacy*.rs` keresesi es riportreteg | `recovery_core.rs`: a beolvasztas generalt koddal bizonyitott. Solvervalaszok kovetkezmenyei: `fast_probe_evidence`, `refinement_evidence`. Riportnezet: `core_view_sound`. | Az utemezes, SMT-kodolas, cvc5, riportkiiras; a `RecoveryDriver` es `coreMachine` megfelelese kezi ellenorzes. |
| `recovery_loop.rs`, `recovery_core.rs` | Generalt ciklusok es beolvasztas; `core_machine_contracts`; `rust_private_recovery_sound`; `example_run`. | Feltetlen terminacio. |
| `lookup*.rs`, `extractor.rs`, `plonkish.rs` | `Recovery/Lookup.lean`: sorszures, oszlopvetites, korrelacio, ures tabla. | A Rust-lookup kodja nem kinyerheto; Halo2-kapuk, masolatok, rotaciok husege. |
| `analyzer.rs`, `analyzable.rs`, SMT encoder/parser/process | Kulso kotelezettsegek a jelenlegi szemantikai tetelekhez. | A Halo2--SMT megfeleles, solvervalaszok ertelmezese, folyamat- es I/O-hibak. |
| Halo2, num-bigint, standard collections, cvc5 | A jelenlegi Rust-futas megbizhato fuggosegei, nem igazolt implementaciok. | Teljes bizonyitasuk kulon projektek vagy explicit elfogadott bizalmi hatar. |

Az osszefoglalo csoportositas nem allitja, hogy a fel nem sorolt
segedfajlok automatikusan bizonyitottak. A mintacircuitek es tesztek nem
helyettesitik a fenti implementacios kotelezettsegeket.

A `global_recovery_reports_sound` a kezzel irt modell tetele. A `core_refines_model`
a kinyert allapotot erre kepezi, igy a modell riporttetelei a konkret futasra is alkalmazhatok.

## A kovetkezo lehetseges lepesek

1. A `run_cached` vezerlesenek kinyerheto, generikus formaba szervezese. Ez nagy refaktor,
   es a kiemelt lepesek bizonyitekat nem helyettesiti.
2. A kovetkeztetesi modulok kinyerese, amikor az Aeneas tamogatja a szukseges konstrukciokat.
3. A cvc5 valaszainak tanusitvanyos ellenorzese.
4. A Halo2 -> UCP/SMT kinyeres husegenek igazolasa.

## A dolgozatban hasznalhato allitas

A pontos megfogalmazast es a bizalmi hatart a [THESIS_CLAIMS.md](THESIS_CLAIMS.md) tartalmazza.
A jelenlegi eredmenyt nem szabad "a teljes Rust-implementacio formalisan verifikalt"
allitaskent bemutatni.
