# Az absztrakt allitasai es a Lean-bizonyitasok

A dokumentum azt rogziti, hogy a dolgozat absztraktjanak formalis verifikaciora
vonatkozo mondatai pontosan mely geppel ellenorzott teteleken alapulnak, es mit
feltetelez a bizonyitas. A tetelnevek a `SourceProof` nevterben vannak, a fajlok
az `aeneas/lean/Proofs/` mappaban talalhatok.

## Ellenorzes

```bash
bash korrekt/verification/aeneas/bootstrap.sh
bash korrekt/verification/aeneas/verify.sh
```

A `verify.sh` az eles Rust-forrasbol ujra kinyeri a Lean-kodot, osszeveti a
rogzitett valtozattal, majd lefordit minden bizonyitast. Az audit minden tetel
tranzitiv axiomait ellenorzi: csak `propext`, `Classical.choice` es `Quot.sound`
engedelyezett. Sem `sorry`, sem sajat axioma nincs.

## Allitasok es tetelek

| Az absztrakt allitasa | Tetel | Fajl | Kotes a Rust-kodhoz |
| --- | --- | --- | --- |
| Az overconstrainedness informacioszivargashoz kapcsolodo ertelmezese | `Overconstrained`, `Determined`, `Consistent` | `PrivateRecovery.lean` | Definicio |
| A QED² helyessegi erveles adaptacioja | `qed2_fixpoint_soundness`, `engine_execution_sound` | `PrivateRecovery.lean`, `EngineFixpoint.lean` | Assign, K- es Delta-frissites generalt kod; tobbi szabaly bizonyitekkal |
| Az erveles atvitele a publikus adat -> privat ertek iranyra | `private_cells_determined_by_public` | `PrivateRecovery.lean` | Mint fent |
| A visszaallitasi eljaras helyessege | `rust_private_recovery_sound`, `core_machine_contracts` | `RecoveryDriver.lean` | Generalt `run_recovery` es `recovery_core` |
| A visszaallitott ertek a valodi titok | `rust_recovery_reveals_secret`, `rust_recovered_value_is_forced` | `PrivateRecovery.lean`, `RecoveryDriver.lean` | Generalt kod |
| A visszaallitas informacioszivargast igazol | `rust_recovery_proves_overconstrained`, `overconstrained_of_cover` | `PrivateRecovery.lean` | Generalt kod |
| A visszaallitas elkulonul a puszta egyertelmusegtol | `rust_unique_cell_has_no_abstract_value`, `rust_assign_marks_unknown_offset_unique`, `rust_rules_reject_cube_equation`, `cube_is_determined_without_rule` | `PrivateRecovery.lean` | Generalt Assign |
| Csak publikus adat a bemenet | `recovery_is_witness_independent` | `PrivateRecovery.lean` | A tetel az eljaras tipusabol kovetkezik; a Rust-bemenet kulon bizalmi pont |
| A tetelek nem uresek | `example_contracts`, `example_run`, `example_recovers_secret`, `example_is_overconstrained` | `Examples.lean` | A generalt kod tenyleges futasa a `ZMod 5` feletti pelda halozaton |

## A bizonyitas bizalmi hatara

A fo tetel feltetelei explicit tetelpremisszak (`OracleContracts`, `EvidenceClaim`,
`EngineStep`). Nem axiomak, de nem is a Rust-kodbol levezetett allitasok:

1. **Halo2-kinyeres.** Az `extractor.rs`, `plonkish.rs`, `lookup_extractor.rs` es az
   SMT-kodolas hu a kapcsolas szemantikajahoz: a `Consistent` halmaz a Halo2-kenyszerek
   tenyleges megoldashalmaza.
2. **SMT-megoldo.** A SAT es UNSAT valaszok jelentese helyes. A cvc5 tanusitvanyat a
   bizonyitas nem ellenorzi. A `fast_probe_evidence` es `refinement_evidence` tetelek
   csak a helyes valaszok kovetkezmenyeit igazoljak.
3. **Szabalymotor.** Az `engine.rs` fixpontja csak `EngineStep` lepeseket hajt vegre. A
   vezerlest a rogzitett Aeneas nem tudja kinyerni, a `value_inference.rs`,
   `linear_domains.rs`, `finite_projection.rs`, `all_but_one.rs`, `base_conv.rs`,
   `bigint_mul.rs` es `lookup.rs` kodja nincs bizonyitva. Ezek matematikai
   helyesseget modellszintu tetelek igazoljak: `all_but_one_rule_evidence`,
   `linear_system_rule_evidence`, `base_conversion_rule_evidence`,
   `Recovery.lookup_column_covers`, `Recovery.root_cell_domain_sound`. A `model_construction.rs`
   modellt javasol es jelolteket zar ki. Kinyert kod helyett a `Recovery/ModelConstruction.lean`
   tetelei igazoljak a matematikat: a javaslatbol csak az eredeti SMT-kodolas SAT-valasza
   lesz minta, a kizaras pedig ugyanarra a szabalyhelyessegre epul, mint a K es a Delta.
4. **Adapter.** A `privacy.rs` `RecoveryDriver` tipusa a kinyert fuggvenyeket hivja, a
   `coreMachine` definicioja ezt a sorrendet koveti. A megfeleles kezi ellenorzes,
   nem tetel. Az utemezes es a riport kiirasa nincs bizonyitva.
5. **Kanonikus domainek.** A motor es a kereses csak normalizalt ertekeket ad at
   (`DomainClaim.canonical`). Ezt ideiglenes futasideju ellenorzes a teljes UCP-tesztkeszletben
   nem cafolta, formalisan nincs igazolva.
6. **Konyvtarak es eszkozok.** A `num-bigint`, a standard gyujtemenyek Lean-modelljei, a
   Rust-fordito, a Charon, az Aeneas es a Lean kernel megbizhato fuggosegek.
7. **Reszleges helyesseg.** A tetelek sikeres lefutasra vonatkoznak. Terminaciot es
   teljesseget nem allitanak: a `NonUnique` vagy `Unresolved` eredmeny nem jelent titkossagot.
   A mintahalmazok meretere a `Headroom` feltetel platformkorlatot kot ki.

## Javasolt megfogalmazas

> Modszerem helyesseget a QED² elemzesi eljaras helyessegi ervelesenek adaptalasaval es
> a privat ertekek visszaallitasara kidolgozott eljaras Lean 4-ben vegzett formalis
> verifikalasaval tamasztom ala: a kovetkeztetesi szabalyok matematikai modelljet, valamint a
> Rust-implementacio focikusat es tudasallapot-kezeleset geppel ellenorzott bizonyitasok
> igazoljak, a Halo2-kinyeres, az SMT-megoldo es a kulso konyvtarak helyesseget feltetelezve.

Nem vallalhato allitas: "a teljes Rust-implementacio formalisan verifikalt".
