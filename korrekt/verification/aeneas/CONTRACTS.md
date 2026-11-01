# A recovery-bizonyitas nyitott implementacios kotelezettsegei

## Mi az uj eredmeny?

A `privacy.rs` tenylegesen a `recovery_loop.rs::run_recovery` fuggvenyt hivja.
Ugyanezt a Rust-kodot nyeri ki a Charon es generalja Leanre az Aeneas.
A `rust_recovery_success_is_sound` a generalt fuggveny sikeres eredmenyerol
bizonyit allapotinvarians-megorzest, explicit muveleti szerzodesek mellett.

A `rust_recovery_preserves_knowledge` ezt a tetelt a kovetkezo invarianssal
instancialja: kielegitheto az eredeti Gamma, K tenyei igazak, a domainek
lefedok, W mintai megvalosithatok, a teljes domainek pontosak, a non-unique
allitasokhoz ket kulonbozo modell tartozik, E pedig Gamma kovetkezmenye.

A generikus allapot es a konkret Rust `UcpResult`/`RecoveryEvidence` kozotti
projekcio megfeleltetese **meg nincs bizonyitva**. Az erre a konkret
adapterre vonatkozo `RecoveryContracts`-erteket a projekt jelenleg nem
allitja elo bizonyitassal. Emiatt a teljes `recover_private_inputs`
implementacios soundnesse meg nem allithato kesz eredmenykent.

## A muveleti szerzodesek

| Muvelet | Elvart allitas | Konkret Rust-kod, amelyre meg bizonyitani kell |
| --- | --- | --- |
| `propagate` | Megorzi a tudasinvarianst; `repeat=false` eseten stabil propagacios allapotot ad. | `propagate_to_fixpoint`, az engine es a teljessegi kanonizalas. |
| `refresh` | Stabil allapotbol helyes, aktualis E/keresesi tenyeket keszit, megorizve a tudast. | `observe_progress`, `established_search_facts`, SMT-premisszak exportja. |
| `select` | Nem rontja a tudast vagy a frissesseget; helyes statuszt ad leallaskor. | `shortlist_actions`, `choose_action`, leallasi okok es keretek. |
| `query` | Megorzi a korabbi tudast; az uj eredmenyhez az eredeti Gamma mellett ervenyes bizonyitek tartozik. | Refine/Discover/FastProbe, solvervalaszok, eredeti kontextus es modellmegosztas. |
| `merge` | Helyes bizonyitekbol helyes tudast keszit; `changed=false` nem hagy el kotelezo propagaciot. | `remember_feasible_samples`, `merge_established_results`, `certify_complete_domains`, non-unique frissites. |

Ezek a szerzodesek panikmentes reszleges specifikaciok: a Rust `Err`
megengedett, de nem jelent sikeres recovery-riportot. A vegtelen futast
nem zarjak ki. A teljes terminaciohoz a konkret muveletek terminaciojat,
valamint a keretekbol vagy csokkeno mertekbol adodo ciklusleallast is
kulon igazolni kell.

A beolvasztas egy konkret resze mar forraskodbol bizonyitott:
`facts.rs::mark_unique` es az inicialis jeloles. A
`rust_assign_then_insert_is_sound` a tenyleges Assign-eredmenyt es a
tenyleges K-frissitest kapcsolja ossze. Ez nem helyettesiti a teljes
`merge` szerzodest: a teljes Delta/W es a tobbi mezofrissites meg nyitott.

A `Proofs/FiniteDomains.lean` a tenyleges `finite_set` ciklusra
terminaciot es teljes-bemenet-megorzest bizonyit. A sikeres some-domain
nem lehet csak a feldolgozott prefix. A konkret konyvtari iteratorok
modelljeire is igazolja a bejarasi szerzodest. Az `intersect` osszes
enum-agara a sikeres eredmeny pontosan a bemeneti halmazok metszete.

A `Proofs/DomainMerge.lean` a tenyleges `mark_domain` lefedesmegorzeset,
a tobbi cella valtozatlansagat, a false eredmenynel teljes valtozatlansagot,
es a korabbi helyes teljessegi igazolasok megorzeset bizonyitja.
A complete agban a bejovo domain vizsgalata nelkul valtozatlan marad az allapot.
Az uj teljessegi jeloles eloallitasa (`try_mark_complete_from_samples`) meg
nincs teljesen bizonyitva. A konkret `RecoveryDriver.merge` osszes frissitesenek
egyuttes invariansmegorzese ettol meg szinten nyitott.

A beolvasztasi tetel kozos egesz reprezentansokra vonatkozik
(`RepresentativeCover`). A `CanonicalMerge.lean` kanonikus bemeneti
domainek mellett most mar modulo-lefedesmegorzest is bizonyit a generalt
mark_domain kodra. A normalizalo hivashelyek invariansat meg igazolni kell;
a puszta modulo-lefedes kanonikussag nelkul nem eleg.
A HashMap/BTreeSet es Iterator modellek helyessege tovabbra is
elfogadott konyvtari szerzodes, nem a standard konyvtar implementacios bizonyitasa.

A `value.rs` konkret `known_value`, `exact_value`, `is_singleton`,
`domain_is_complete`, `for_hypothetical_reasoning` es `bounded_value`
fuggvenyeit is kinyeri. A `Proofs/DomainState.lean` ezeken bizonyitja:

- Lefedes es kezdeti SAT mellett a visszaadott exact ertek kotelezo.
- A complete-lekerdezes pontosan az Exact alaktagot vagy a tarolt
  explicit igazolast hasznalja; hianyzo domain nem lesz complete.
- Az explicit teljessegi igazolasok helyesseget feltetelezve a
  complete-lekerdezes valoban a teljes megvalosithato ertekhalmazt jeloli.
- A hipotetikus masolat valtozatlan domaineket es ures teljessegi
  jeloleshalmazt keszit. Erosebb kontextusban a lefedes megmarad;
  a tobbjeloltes domain nem orokli az eredeti megvalosithatosagi igazolast.
- A bitkorlat megorzott erteket vagy None-t ad, soha nem csonkolt erteket.

Ez a tenyleges tarolo olvasasi es masolasi kodjanak bizonyitasa,
nem a `try_mark_complete_from_samples` teljes irasi muvelete. A
`CompletionFlagsSound` az utobbi muveletre meg bizonyitando invarians,
nem uj axioma. A HashMap/BTreeSet-klonozas es a BigInt `bits()`
konyvtari modelljeinek Rust-husege tovabbra is bizalmi feltetel.

A korabbi Iterator-kinyeresi hiba a `cloned()` azonosszemantikaju
`map(|value| value.clone())` alakjaval es a dokumentalt traitmezofilterrel
megkerulheto. A teljes mark_domain torzs es a hivasgrafja most kinyert kod;
a `mergeDomainTail` bizonyitasbeli kiemelesre csak Lean altal ellenorzott
definicios egyenloseggel lep at, nem feltetelezett helyettesitessel.

A `normalize_field_value` teljes kivalasztott torzse is kinyert es
megfelelesi/soundness-tetelekkel ellenorzott. A kulso BigInt-muveletek
modelljere epul; nem a num-bigint implementacioja bizonyitott.

A teljessegjeloles kinyeresi akadalyat a vec! makro helyetti biztonsagos
vektorepites es a diagnosztikai wrapper levalasztasa oldja fel. Az eles
`try_mark_complete_from_samples` torzse/ciklusa most generalt kod.
A `CertificationControl.lean` konkret hiba- es jeloltfrissitesi lepeseit
ellenorzi, de a teljes ciklus mintalefedesi invariansa meg nyitott.
A normalizalt halmazok reszhalmaz/elemszam kriteriumanak szemantikai tetele
kesz; annak alkalmazasat a teljes generalt ciklusra meg bizonyitani kell.

## Mit nem helyettesit az audit?

Az audit megakadalyozza a `sorryAx`, sajat axiomak es `native_decide`
rejtett hasznalatat. Nem bizonyitja a Rust-konyvtari modellek huseget,
nem igazolja a Halo2--UCP kinyerest, es nem zarja be a fenti szerzodeseket.
A forrashash az aktualis fajlverziot rogziti, nem onallo helyessegbizonyitas.

## Futtatott ellenorzesek

- Charon/Aeneas kinyeres a tenyleges szabalyokbol es recovery-fociklusbol.
- Lean-build es tranzitiv axiomaaudit.
- A recovery-ciklus sajat sorrend-, ujrainditas- es hibaagtesztjei.
- A meglevo privacy-regressziok az eles adapterrel.

Az eredeti teljes fuggveny kozvetlen kinyeresi probaja a pinned Aeneasban
`Continue to outer loops are not supported yet` hibaval allt meg;
iterator/closure tipusoknal tovabbi frontend-hibak is jelentkeztek.
Ezek miatt tortent a kozos, elesben is hasznalt vezerlomodul kiemelese.
