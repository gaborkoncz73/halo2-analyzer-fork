//! Egy vállalati kosár számláját, kuponját és beszállítói bontását ellenőrzi.
//! A publikus összesítőket ugyanazokból a privát termékmennyiségekből számítja.

use crate::{
    circuit_analyzer::{halo2_proofs_libs::*, ucp::cell::CellId},
    io::analyzer_io_type::{AnalyzerInput, LookupMethod, VerificationInput, VerificationMethod},
};
use std::array;

pub(super) const K: u32 = 7;
pub(super) const ALL: u8 = 15;
pub(super) const PRICES: [u64; 4] = [1200, 2500, 1800, 900];
pub(super) const WEIGHTS: [u64; 4] = [500, 1000, 700, 200];
pub(super) const POINTS: [u64; 4] = [2, 5, 4, 1];
pub(super) const COUPONS: [u64; 5] = [0, 5, 10, 10, 15];
pub(super) const SHIPPING: [[u64; 4]; 3] = [
    [0, 0, 50_000, 600],
    [1, 50_001, 100_000, 1200],
    [2, 100_001, 200_000, 2000],
];
pub(super) const OBSERVED: [u64; 4] = [124, 71_600, 352, 208_148];
pub(super) const SUMMARY_ROW: usize = 4;
pub(super) const INVOICE_ROW: usize = 5;
pub(super) const SUPPLIER_ROW: usize = 6;
pub(super) const LEDGER_ROW: usize = 7;
const RANGE_START: usize = 8;
const ROWS: usize = 13;
const COLUMNS: usize = 16;

// A számlasor oszlopneveihez ugyanazokat a cellaazonosítókat rendeli a tesztekben is.
pub(super) const SUBTOTAL: usize = 0;
pub(super) const COUPON: usize = 1;
pub(super) const RATE: usize = 2;
pub(super) const DISCOUNT: usize = 3;
pub(super) const DISCOUNT_REMAINDER: usize = 4;
pub(super) const TAX_BASE: usize = 5;
pub(super) const TAX: usize = 6;
pub(super) const TAX_REMAINDER: usize = 7;
pub(super) const SHIPPING_FEE: usize = 8;
pub(super) const SHIPPING_CLASS: usize = 9;
const LOWER: usize = 10;
const UPPER: usize = 11;
const LOWER_SLACK: usize = 12;
const UPPER_SLACK: usize = 13;
pub(super) const GROSS: usize = 14;
const TOTAL_WEIGHT: usize = 15;

#[derive(Clone, Debug)]
pub(super) struct CartWitness {
    pub quantities: [u64; 4],
    pub coupon: usize,
    pub supplier_u: u64,
}

impl Default for CartWitness {
    fn default() -> Self {
        Self {
            quantities: [37, 29, 25, 33],
            coupon: 2,
            supplier_u: 4,
        }
    }
}

impl CartWitness {
    pub(super) fn rows(&self) -> [[u64; COLUMNS]; ROWS] {
        let mut rows = [[0; COLUMNS]; ROWS];
        for (i, quantity) in self.quantities.into_iter().enumerate() {
            rows[i][0] = quantity;
            for bit in 0..7 {
                rows[i][1 + bit] = (quantity >> bit) & 1;
            }
            rows[i][8] = quantity * PRICES[i];
            rows[i][9] = quantity * WEIGHTS[i];
            rows[i][10] = quantity * POINTS[i];
        }
        let total = self.quantities.iter().sum();
        let subtotal: u64 = (0..4).map(|i| rows[i][8]).sum();
        let weight: u64 = (0..4).map(|i| rows[i][9]).sum();
        let points = (0..4).map(|i| rows[i][10]).sum();
        let shipping = SHIPPING
            .iter()
            .find(|s| s[1] <= weight && weight <= s[2])
            .expect("A tanúpélda tömege a megadott szállítási sávba esik");
        let rate = COUPONS[self.coupon];
        let discount = subtotal * rate / 100;
        let base = subtotal - discount + 17;
        let tax = base * 20 / 100;
        rows[SUMMARY_ROW][4..8].copy_from_slice(&[total, weight, points, subtotal]);
        rows[INVOICE_ROW] = [
            subtotal,
            self.coupon as u64,
            rate,
            discount,
            subtotal * rate % 100,
            base,
            tax,
            base * 20 % 100,
            shipping[3],
            shipping[0],
            shipping[1],
            shipping[2],
            weight - shipping[1],
            shipping[2] - weight,
            base + tax + shipping[3],
            weight,
        ];
        rows[SUPPLIER_ROW][..3].copy_from_slice(&[
            self.quantities[0],
            self.supplier_u,
            self.quantities[0] - self.supplier_u,
        ]);
        rows[LEDGER_ROW][shipping[0] as usize] = shipping[3];
        rows[LEDGER_ROW][3] = shipping[0];
        rows[LEDGER_ROW][4] = shipping[3];
        for (i, column) in [DISCOUNT, TAX_BASE, TAX, LOWER_SLACK, UPPER_SLACK]
            .into_iter()
            .enumerate()
        {
            let value = rows[INVOICE_ROW][column];
            rows[RANGE_START + i][0] = value;
            for digit in 0..5 {
                rows[RANGE_START + i][1 + digit] = (value >> (4 * digit)) & 15;
            }
        }
        rows
    }

    pub fn observations(&self) -> [u64; 4] {
        let rows = self.rows();
        [
            rows[SUMMARY_ROW][4],
            rows[SUMMARY_ROW][5],
            rows[SUMMARY_ROW][6],
            rows[INVOICE_ROW][GROSS],
        ]
    }
}

#[derive(Clone, Default)]
pub(super) struct InvoiceAudit<const OBS: u8> {
    pub witness: Option<CartWitness>,
    pub tamper: Option<(usize, usize, u64)>,
}

impl<const OBS: u8> InvoiceAudit<OBS> {
    pub fn new(witness: CartWitness) -> Self {
        Self {
            witness: Some(witness),
            tamper: None,
        }
    }

    pub fn instances(&self) -> Vec<Vec<Fr>> {
        vec![self
            .witness
            .as_ref()
            .unwrap()
            .observations()
            .map(Fr::from)
            .to_vec()]
    }

    pub fn input(&self) -> AnalyzerInput {
        let observations = self.witness.as_ref().unwrap().observations();
        AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput::new(
                observations
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| OBS & (1 << i) != 0)
                    .map(|(i, value)| (format!("I-0-{i}"), value as i64)),
                1,
            ),
            lookup_method: LookupMethod::InlineConstraints,
        }
    }
}

pub(super) fn invoice_cell(column: usize) -> CellId {
    CellId::advice(column, INVOICE_ROW as i32)
}

pub(super) fn target_name(cell: &CellId) -> &'static str {
    match cell.row as usize {
        0..=3 => ["q_paper", "q_coffee", "q_cleaner", "q_cable"][cell.row as usize],
        INVOICE_ROW => [
            "subtotal_B",
            "coupon_c",
            "discount_percent_d",
            "discount_D",
            "discount_remainder",
            "tax_base_E",
            "tax_V",
            "tax_remainder",
            "shipping_fee_S",
            "shipping_class_k",
        ][cell.column],
        SUPPLIER_ROW => ["q_paper_copy", "supplier_u", "supplier_v"][cell.column],
        LEDGER_ROW => ["carrier_S0", "carrier_S1", "carrier_S2"][cell.column],
        _ => unreachable!("Csak a kijelölt célcellákhoz rendel nevet"),
    }
}

pub(super) fn targets() -> Vec<CellId> {
    (0..4)
        .map(|row| CellId::advice(0, row))
        .chain(
            [
                SUBTOTAL,
                COUPON,
                RATE,
                DISCOUNT,
                DISCOUNT_REMAINDER,
                TAX_BASE,
                TAX,
                TAX_REMAINDER,
                SHIPPING_FEE,
                SHIPPING_CLASS,
            ]
            .map(invoice_cell),
        )
        .chain([
            CellId::advice(1, SUPPLIER_ROW as i32),
            CellId::advice(2, SUPPLIER_ROW as i32),
        ])
        .chain((0..3).map(|col| CellId::advice(col, LEDGER_ROW as i32)))
        .collect()
}

#[derive(Clone)]
pub(super) struct InvoiceConfig {
    advice: [Column<Advice>; COLUMNS],
    public: Column<Instance>,
    fixed: [Column<Fixed>; 3],
    selectors: [Selector; 6],
    tables: [TableColumn; 10],
}

impl<const OBS: u8> Circuit<Fr> for InvoiceAudit<OBS> {
    type Config = InvoiceConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let advice = array::from_fn(|_| meta.advice_column());
        let public = meta.instance_column();
        let fixed = array::from_fn(|_| meta.fixed_column());
        let selectors = array::from_fn(|_| meta.complex_selector());
        let tables = array::from_fn(|_| meta.lookup_table_column());
        for column in advice {
            meta.enable_equality(column);
        }
        meta.enable_equality(public);
        let c = |v| Expression::Constant(Fr::from(v));

        meta.create_gate("catalog lines and seven-bit quantities", |meta| {
            let q = meta.query_selector(selectors[0]);
            let quantity = meta.query_advice(advice[0], Rotation::cur());
            let mut equations = vec![
                quantity.clone()
                    - (0..7).fold(c(0), |sum, bit| {
                        sum + c(1 << bit) * meta.query_advice(advice[1 + bit], Rotation::cur())
                    }),
            ];
            for bit in 0..7 {
                let b = meta.query_advice(advice[1 + bit], Rotation::cur());
                equations.push(b.clone() * (b - c(1)));
            }
            for i in 0..3 {
                equations.push(
                    meta.query_advice(advice[8 + i], Rotation::cur())
                        - quantity.clone() * meta.query_fixed(fixed[i]),
                );
            }
            equations
                .into_iter()
                .map(|e| q.clone() * e)
                .collect::<Vec<_>>()
        });
        // A négy terméksort valódi negatív rotációkkal éri el, nem másolt összesítő konstansokkal.
        meta.create_gate("cart totals across product rows", |meta| {
            let q = meta.query_selector(selectors[1]);
            [0, 9, 10, 8]
                .into_iter()
                .enumerate()
                .map(|(i, source)| {
                    q.clone()
                        * (meta.query_advice(advice[4 + i], Rotation::cur())
                            - (1..=4).fold(c(0), |sum, offset| {
                                sum + meta.query_advice(advice[source], Rotation(-offset))
                            }))
                })
                .collect::<Vec<_>>()
        });
        meta.create_gate("discount rounding tax and shipping", |meta| {
            let q = meta.query_selector(selectors[2]);
            let a: Vec<_> = advice
                .iter()
                .map(|col| meta.query_advice(*col, Rotation::cur()))
                .collect();
            vec![
                a[RATE].clone() * a[SUBTOTAL].clone()
                    - c(100) * a[DISCOUNT].clone()
                    - a[DISCOUNT_REMAINDER].clone(),
                a[TAX_BASE].clone() - a[SUBTOTAL].clone() + a[DISCOUNT].clone()
                    - meta.query_fixed(fixed[0]),
                c(20) * a[TAX_BASE].clone() - c(100) * a[TAX].clone() - a[TAX_REMAINDER].clone(),
                a[GROSS].clone() - a[TAX_BASE].clone() - a[TAX].clone() - a[SHIPPING_FEE].clone(),
                a[TOTAL_WEIGHT].clone() - a[LOWER].clone() - a[LOWER_SLACK].clone(),
                a[UPPER].clone() - a[TOTAL_WEIGHT].clone() - a[UPPER_SLACK].clone(),
            ]
            .into_iter()
            .map(|e| q.clone() * e)
            .collect::<Vec<_>>()
        });
        meta.create_gate("supplier packaging", |meta| {
            let q = meta.query_selector(selectors[3]);
            vec![
                q * (meta.query_advice(advice[0], Rotation::cur())
                    - meta.query_advice(advice[1], Rotation::cur())
                    - meta.query_advice(advice[2], Rotation::cur())),
            ]
        });
        meta.create_gate("carrier ledger allocation", |meta| {
            let q = meta.query_selector(selectors[4]);
            let k = meta.query_advice(advice[3], Rotation::cur());
            let mut equations = vec![
                (0..3).fold(c(0), |sum, i| {
                    sum + meta.query_advice(advice[i], Rotation::cur())
                }) - meta.query_advice(advice[4], Rotation::cur()),
            ];
            for i in 0..3 {
                equations.push(
                    meta.query_advice(advice[i], Rotation::cur()) * (k.clone() - c(i as u64)),
                );
            }
            equations
                .into_iter()
                .map(|e| q.clone() * e)
                .collect::<Vec<_>>()
        });
        meta.create_gate("unsigned twenty-bit amounts", |meta| {
            let q = meta.query_selector(selectors[5]);
            vec![
                q * (meta.query_advice(advice[0], Rotation::cur())
                    - (0..5).fold(c(0), |sum, digit| {
                        sum + c(1 << (4 * digit))
                            * meta.query_advice(advice[1 + digit], Rotation::cur())
                    })),
            ]
        });

        // A kikapcsolt lookupokat a tábla első sorára képezi; azok nem szűkítik az advice cellákat.
        for (selector, column, table, default) in [
            (2, DISCOUNT_REMAINDER, 1, 0),
            (2, TAX_REMAINDER, 1, 0),
            (3, 1, 2, 0),
            (3, 2, 3, 0),
            (5, 1, 0, 0),
            (5, 2, 0, 0),
            (5, 3, 0, 0),
            (5, 4, 0, 0),
            (5, 5, 0, 0),
        ] {
            meta.lookup(|meta| {
                let q = meta.query_selector(selectors[selector]);
                vec![(
                    q.clone() * meta.query_advice(advice[column], Rotation::cur())
                        + (c(1) - q) * c(default),
                    tables[table],
                )]
            });
        }
        meta.lookup(|meta| {
            let q = meta.query_selector(selectors[2]);
            [(COUPON, 4), (RATE, 5)]
                .into_iter()
                .map(|(column, table)| {
                    (
                        q.clone() * meta.query_advice(advice[column], Rotation::cur()),
                        tables[table],
                    )
                })
                .collect::<Vec<_>>()
        });
        meta.lookup(|meta| {
            let q = meta.query_selector(selectors[2]);
            [SHIPPING_CLASS, LOWER, UPPER, SHIPPING_FEE]
                .into_iter()
                .enumerate()
                .map(|(i, column)| {
                    (
                        q.clone() * meta.query_advice(advice[column], Rotation::cur())
                            + (c(1) - q.clone()) * c(SHIPPING[0][i]),
                        tables[6 + i],
                    )
                })
                .collect::<Vec<_>>()
        });
        InvoiceConfig {
            advice,
            public,
            fixed,
            selectors,
            tables,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "public catalog domains",
            |mut table| {
                // A maradéktáblához igazítja a kisebb relációkat, új tuple hozzáadása nélkül.
                for row in 0..100 {
                    let shipping = SHIPPING[row % 3];
                    let values = [
                        (row % 16) as u64,
                        (row % 100) as u64,
                        2 * (row % 31) as u64,
                        3 * (row % 22) as u64,
                        (row % 5) as u64,
                        COUPONS[row % 5],
                        shipping[0],
                        shipping[1],
                        shipping[2],
                        shipping[3],
                    ];
                    for (column, value) in config.tables.into_iter().zip(values) {
                        table.assign_cell(
                            || "allowed entry",
                            column,
                            row,
                            || Value::known(Fr::from(value)),
                        )?;
                    }
                }
                Ok(())
            },
        )?;
        let data = self.witness.as_ref().map(CartWitness::rows);
        let exposed = layouter.assign_region(
            || "connected invoice audit",
            |mut region| {
                let mut cells = Vec::new();
                for row in 0..ROWS {
                    let selector = match row {
                        0..=3 => 0,
                        4 => 1,
                        5 => 2,
                        6 => 3,
                        7 => 4,
                        _ => 5,
                    };
                    config.selectors[selector].enable(&mut region, row)?;
                    let columns = match row {
                        0..=3 => 11,
                        4 => 8,
                        5 => 16,
                        6 => 3,
                        7 => 5,
                        _ => 6,
                    };
                    let mut assigned = Vec::new();
                    for column in 0..columns {
                        let value = data.as_ref().map(|rows| rows[row][column]);
                        let value = if let Some((r, col, replacement)) = self.tamper {
                            if (r, col) == (row, column) {
                                Some(replacement)
                            } else {
                                value
                            }
                        } else {
                            value
                        };
                        assigned.push(region.assign_advice(
                            || "invoice witness",
                            config.advice[column],
                            row,
                            || {
                                value
                                    .map(|v| Value::known(Fr::from(v)))
                                    .unwrap_or(Value::unknown())
                            },
                        )?);
                    }
                    cells.push(assigned);
                    if row < 4 {
                        for (column, value) in
                            config
                                .fixed
                                .into_iter()
                                .zip([PRICES[row], WEIGHTS[row], POINTS[row]])
                        {
                            region.assign_fixed(
                                || "published product attribute",
                                column,
                                row,
                                || Value::known(Fr::from(value)),
                            )?;
                        }
                    }
                }
                region.assign_fixed(
                    || "fixed handling fee",
                    config.fixed[0],
                    INVOICE_ROW,
                    || Value::known(Fr::from(17)),
                )?;
                for ((r1, c1), (r2, c2)) in [
                    ((SUMMARY_ROW, 7), (INVOICE_ROW, SUBTOTAL)),
                    ((SUMMARY_ROW, 5), (INVOICE_ROW, TOTAL_WEIGHT)),
                    ((0, 0), (SUPPLIER_ROW, 0)),
                    ((INVOICE_ROW, SHIPPING_CLASS), (LEDGER_ROW, 3)),
                    ((INVOICE_ROW, SHIPPING_FEE), (LEDGER_ROW, 4)),
                ] {
                    region.constrain_equal(cells[r1][c1].cell(), cells[r2][c2].cell())?;
                }
                for (i, column) in [DISCOUNT, TAX_BASE, TAX, LOWER_SLACK, UPPER_SLACK]
                    .into_iter()
                    .enumerate()
                {
                    region.constrain_equal(
                        cells[INVOICE_ROW][column].cell(),
                        cells[RANGE_START + i][0].cell(),
                    )?;
                }
                Ok([
                    cells[SUMMARY_ROW][4].clone(),
                    cells[SUMMARY_ROW][5].clone(),
                    cells[SUMMARY_ROW][6].clone(),
                    cells[INVOICE_ROW][GROSS].clone(),
                ])
            },
        )?;
        for (i, cell) in exposed.into_iter().enumerate() {
            if OBS & (1 << i) != 0 {
                layouter.constrain_instance(cell.cell(), config.public, i)?;
            }
        }
        Ok(())
    }
}
