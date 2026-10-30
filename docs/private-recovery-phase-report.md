# Visszaállítási Fázisnapló

A normál példakimenet a recovery tényleges sorrendjét mutatja. A számlapélda
és a settlement-audit alapértelmezetten ezt írja ki, nem a profilozási számlálókat
és a teljes belső riportot. A futtatási parancsok változatlanok:

```bash
cargo test --offline -p korrekt --lib thesis_invoice_recovery_smoke -- --ignored --nocapture --test-threads=1
cargo test --offline -p korrekt --lib settlement_audit_ -- --nocapture --test-threads=1
```

A két parancsot egymás után kell futtatni, nem egyszerre: az SMT-fájlok közösek.

## A Blokkok Jelentése

```text
Initial SAT: VerifiedWitness; 0 solver calls

1. UCP (... s)
  Targets: 16 exact values, 3 domains. New: 16 exact, 3 new/refined domains.
  q_paper = 37 (exact)
  ...
  coupon_c in {2, 3} (covering domain)

1. SMT (... s; 8 solver calls)
  Refine/FastProbe: supplier_u; 2 calls (FastProbe: 2)
    New feasible samples: ...
    supplier_u; non-unique proven
  ...
  Refine/Candidates: supplier_u; 1 call (Coverage: 1)
    No new target or queried-cell facts.
    Limitation: SolverTimeout
  ...
  Targets: 16 exact values, 3 domains; 17 complete domains, 3 non-unique.
  No UCP restart: K/Delta contents unchanged.
```

- A darabszámok csak a kijelölt privát célokra vonatkoznak. Nem számolja bele
  a publikus/fixed cellákat vagy az összes belső segédváltozót.
- Az `exact values` egyelemű domaineket jelent; a külön `domains` mező csak
  a többértékű lefedő domaineket számolja. A fejléc az aktuális teljes állapotot,
  a `New` rész az adott UCP-fázis változásait mutatja.
- Az egyes cellák sorai külön jelzik az érték/domain változását, a
  nemegyértelműség bizonyítását és a domain teljességének igazolását.
- A `New feasible samples` az adott SMT-lépésben újonnan megőrzött értékeket
  jelenti. Ezek önmagukban nem lefedő domainek, és külön cellák mintái nem
  alkotnak automatikusan közös kielégítő értékadást.
- A köztes, nem célként kijelölt cellát `(bridge)` jelöli. Ennek új értéke
  látható, de a kijelölt célok darabszámát nem növeli.

A szomszédos SMT-műveletek egy blokkba kerülnek, amíg nem indul valódi új
propagáció. Ha az SMT új K/Delta-tényt ad át, a következő blokk `2. UCP`, majd
újabb keresés esetén `2. SMT`. A puszta új minták, nemegyértelműségi bizonyíték
és teljességi metaadat nem hoz létre fiktív UCP-blokkot. Az aktuális számlapélda
ezért csak `1. UCP` és `1. SMT` blokkot ad; a settlement-audit valódi
UCP/SMT/UCP visszacsatolást is mutat.

A külön `settlement_audit_refinement_restarts_long_ucp_chain` tesztben
ellenőrzött sorozat:

```text
1. UCP: 7 exact values, 12 domains
1. SMT: 3 solver calls; one amount bit recovered
2. UCP: 22 exact values, 3 domains; 14 new exact values
2. SMT: 25 solver calls; the remaining three domains completed
3. UCP: no new target facts
```

A kezdeti külön SAT-hívással együtt ez 29 solverfolyamat. A napló a tényleges
kiválasztást mutatja: itt nem a tarifakód, hanem az összeg egyik bitje indítja
el az első SMT/UCP visszacsatolást. Az ütemezés más beállításokkal változhat.

## Solverhívások

A `calls` a tényleges solverfolyamatok száma, nem a szemantikai cellapróbáké.
A számlapélda ellenőrzött futásában három fast-probe művelet összesen hat
solverhívást végzett, majd két lefedésvizsgálat összesen kettőt. A két utóbbi
timeoutolt; ez nem törölte a már bizonyított pontos értékeket vagy a
nemegyértelműséget, és a napló a korlátot külön megmutatja.

| Hívástípus | Jelentés |
| --- | --- |
| `FastProbe` | Belső pontosérték/egyértelműségi stratégia; több solverfolyamatot, fallbacket is tartalmazhat |
| `Coverage` | Az eredeti kontextusban kizárja a domainen kívüli értékeket |
| `CandidateFeasibility` | Egy konkrét domainjelölt megvalósíthatóságát vizsgálja |
| `Enumeration` | Korábbi minták kizárásával új teljes modellértéket keres |
| `SubsetExclusion` | Az eredeti kényszerek kiválasztott részhalmazán vizsgál kizárást; SAT-mintát innen nem vesz át |

A kezdeti SAT-guard külön soron szerepel, a normál UCP/SMT-számozás előtt.
Az opcionális szerkezeti baseline szintén nem recovery-fázis. A teljes API-idő
előkészítést, SAT-guardot, ütemezést és külön kért kontrollt is tartalmazhat,
ezért nem feltétlenül egyezik a recovery-fázisidők összegével.
Az ezen kívüli időt az `Other work` sor külön mutatja, a teljes API-idő és
a recovery-fázisidők különbségeként. Ez nem további, elrejtett solverhívás-számláló.
A heurisztikus és feltételes UCP-szimulációkat nem mutatja önálló, igazolt
recovery-körként.

## API És Részletes Nézet

```rust
println!("{}", report.phase_report());
println!("{}", report.phase_report_with_names(|cell| names.get(cell).cloned()));
```

A `report.phases` strukturált `RecoveryPhase` eseményeket tartalmaz.
Az eseményeket a tényleges műveletek mellett rögzíti, nem a végső összesítőből
próbálja utólag kitalálni a sorrendet. A szöveget a hívó a futás után írja ki;
a könyvtár nem nyomtat önállóan, és nem indít új elemzést a megjelenítéshez.
Az új `report.solver_invocations` a kezdeti guardot is tartalmazó tényleges
folyamatszám. A meglévő szemantikai és domainkeresési keretszámlálók jelentése
nem változott. A megfigyelés a jelenlegi szinkron solverútvonal szálán számol.
A megjelenítési regressziók a fázissorrendet, a valódi folyamatdarabszámot,
a célcellákra korlátozott összesítést, a teljesség miatti fiktív újraindítás
elkerülését és a véges halmazok korlátos előnézetét ellenőrzik.
A teljes könyvtári tesztkészlet 484 sikeres, 0 hibás és 10 szándékosan kihagyott
teszttel zárult; a külön számlamérés és a settlement-visszacsatolásos futás is
sikeres. A módosítás nem vezetett be új inference-szabályt vagy solverkérdést.

A régi részletes gépi sorok és a számlapélda profilozása:

```bash
UCP_DEMO_VERBOSE=1 cargo test --offline -p korrekt --lib thesis_invoice_recovery_smoke -- --ignored --nocapture --test-threads=1
```

A nyilvános `Display` formátum továbbra is a teljes riportot adja. A normál
példakimenet a tömör fázisnézetet használja; a megjelenített véges halmazok
előnézete legfeljebb nyolc érték, miközben a strukturált domain teljes marad.
