# A recovery-bizonyitas szerzodesei

## Az eredmeny

A korabban nyitott `RecoveryContracts` kotelezettseg most bizonyitott a konkret
`coreMachine` gepre (`core_machine_contracts`). A gep a generalt `run_recovery`
fociklust a generalt `merge_established_evidence`, `finish_merge` es
`try_certify_complete_domains` fuggvenyekkel futtatja, ugyanabban a sorrendben, mint a
`privacy.rs` `RecoveryDriver` adaptere.

A fo tetel `rust_private_recovery_sound`. Sikeres visszateresnel a teljes allapot
`CoreSound` invariansa es a `SoundRecovery` riportnezet igaz: K tenyei, a lefedo
domainek, a W-mintak, a teljessegi jelolesek es a non-unique cimkek az eredeti
kontextusra helyesek. A dolgozat fogalmaira a `PrivateRecovery.lean` viszi at.

## Amit az orakulum szerzodese kikot

Az `OracleContracts` a megmaradt, kodbol nem levezetett kotelezettsegeket nevezi meg:

| Muvelet | Elvart allitas | Eles Rust-kod |
| --- | --- | --- |
| `engine` | A K/Delta valtozasa `EngineStep` lepesek veges sorozata. | `engine.rs::run_cached`, a kovetkeztetesi modulok |
| `refresh` | A keresesi premisszak az eredeti kontextus kovetkezmenyei. | `observe_progress`, `established_search_facts` |
| `select` | Nem rontja a keresesi premisszakat, helyes leallasi statuszt ad. | `shortlist_actions`, `choose_action` |
| `query` | Az eredmenyre teljesul az `EvidenceClaim`. | `refine_domain`, `discover_domain`, cvc5 |
| `admin` | A nem szemantikus adminisztracio megorzi a premisszakat. | `merge_established_results` retry- es korlatkezelese |

Az `EvidenceClaim` a beolvasztando eredmeny bizonyitasi kotelezettsege: a mintak
megvalosithatok, a domain lefedo es kanonikus, a unique es non-unique cimkek igazoltak.
A `fast_probe_evidence` es a `refinement_evidence` megmutatja, hogy helyes SAT- es
UNSAT-valaszokbol ez kovetkezik.

Az `EngineStep` negy lepese: generalt Assign, generalt `mark_domain` igazolt domainnel,
singletonbol egyertelmuseg, valamint igazolt egyertelmusegi szabaly. A
`all_but_one_rule_evidence`, `linear_system_rule_evidence` es
`base_conversion_rule_evidence` modellszintu bizonyitekot ad a szabalyokhoz.
A lookup-szabaly modellje a `Recovery/Lookup.lean`.

## Mit nem bizonyit a tetel

- A `run_cached` valoban csak `EngineStep` lepeseket hajt vegre. A vezerles nem kinyerheto.
- A kovetkeztetesi modulok kodja a modellszintu teteleknek megfelel.
- A `RecoveryDriver` a `coreMachine` szerint mukodik. Ez kezi ellenorzes.
- A cvc5 valaszai es az SMT-kodolas helyesek.
- A Halo2-kinyeres hu a kapcsolashoz.
- A futas terminal.

A `Headroom` premissza kizarja, hogy egy mintahalmaz merete tullepje a platform `usize`
tartomanyat. A korlatlan Lean-modellben ez kulon feltetel, a fizikai memoriaban nem fordulhat elo.

## Mit nem helyettesit az audit?

Az audit a `sorryAx`, a sajat axiomak es a `native_decide` rejtett hasznalatat zarja ki.
Nem bizonyitja a konyvtari modellek huseget, es nem zarja be az orakulum szerzodeset.
A forrashash az aktualis fajlverziot rogziti, nem onallo helyessegbizonyitas.

## Futtatott ellenorzesek

- Charon/Aeneas kinyeres az eles forrasbol, `verify.sh`.
- Lean-build es tranzitiv axiomaaudit mindket csomagon.
- Nem-uressegi pelda: `example_run` a generalt kodot tenylegesen lefuttatja.
- Mutacios proba: a `recovery_core.rs`, `value.rs` es `expr.rs` szandekosan elrontott
  valtozatain a bizonyitasok vagy a kinyeres-ellenorzes elbukott.
- A meglevo UCP-regressziok egyszalu futtatassal: `cargo test -p korrekt --lib ucp:: -- --test-threads=1`.

## A kinyeres korlatai

A pinned Aeneas az eredeti `recover_private_inputs` kozvetlen kinyereseben a
`Continue to outer loops are not supported yet` hibaval allt meg, a `value_inference.rs`
kodjan pedig a beagyazott return, a korai kilepes es a fuggvenytipusok miatt.
Ezert kerult a fociklus a `recovery_loop.rs`, a beolvasztas a `recovery_core.rs` modulba.
Az eles adapter ugyanezt a kodot hivja.
