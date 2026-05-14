use group::ff::PrimeField;
use std::marker::PhantomData;

use zcash_halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use zcash_halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Error, Expression, Instance, Selector,
};
use zcash_halo2_proofs::poly::Rotation;

// ===== UNDERCONSTRAINED DECODER =====

#[derive(Clone)]
pub struct UnderDecoderConfig<const W: usize = 4> {
    inp: Column<Advice>,
    out: [Column<Advice>; W],
    success: Column<Advice>,

    inp_instance: Column<Instance>,

    s: [Selector; W],
    s_success: Selector,
}

pub struct UnderDecoderCircuit<F: PrimeField, const W: usize = 4>(pub PhantomData<F>);

impl<F: PrimeField, const W: usize> Default for UnderDecoderCircuit<F, W> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<F: PrimeField, const W: usize> Circuit<F> for UnderDecoderCircuit<F, W> {
    type Config = UnderDecoderConfig<W>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self(PhantomData)
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> UnderDecoderConfig<W> {
        let inp = meta.advice_column();
        let out = std::array::from_fn(|_| meta.advice_column());
        let success = meta.advice_column();

        let inp_instance = meta.instance_column();

        meta.enable_equality(inp);
        meta.enable_equality(inp_instance);

        let s = std::array::from_fn(|_| meta.selector());
        let s_success = meta.selector();

        for i in 0..W {
            meta.create_gate("under_decoder", |meta| {
                let selector = meta.query_selector(s[i]);
                let inp_q = meta.query_advice(inp, Rotation::cur());
                let out_q = meta.query_advice(out[i], Rotation::cur());
                let i_const = Expression::Constant(F::from(i as u64));

                vec![selector * out_q * (inp_q - i_const)]
            });
        }

        meta.create_gate("under_decoder_success", |meta| {
            let selector = meta.query_selector(s_success);
            let success_q = meta.query_advice(success, Rotation::cur());

            let sum = (0..W).fold(Expression::Constant(F::ZERO), |acc, i| {
                acc + meta.query_advice(out[i], Rotation::cur())
            });

            vec![selector * (success_q - sum)]
        });

        meta.create_gate("success_boolean", |meta| {
            let selector = meta.query_selector(s_success);
            let success_q = meta.query_advice(success, Rotation::cur());
            let one = Expression::Constant(F::ONE);

            vec![selector * success_q.clone() * (success_q - one)]
        });

        UnderDecoderConfig {
            inp,
            out,
            success,
            inp_instance,
            s,
            s_success,
        }
    }

    fn synthesize(
        &self,
        config: UnderDecoderConfig<W>,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let inp_cell = layouter.assign_region(
            || "underconstrained decoder",
            |mut region| {
                let inp_cell = region.assign_advice(
                    || "inp",
                    config.inp,
                    0,
                    || Value::known(F::from(2u64)),
                )?;

                for i in 0..W {
                    config.s[i].enable(&mut region, 0)?;

                    region.assign_advice(
                        || format!("out{}", i),
                        config.out[i],
                        0,
                        || Value::known(F::ZERO),
                    )?;
                }

                config.s_success.enable(&mut region, 0)?;

                region.assign_advice(
                    || "success",
                    config.success,
                    0,
                    || Value::known(F::ZERO),
                )?;

                Ok(inp_cell)
            },
        )?;

        layouter.constrain_instance(inp_cell.cell(), config.inp_instance, 0)?;

        Ok(())
    }
}

// ===== CORRECT DECODER =====


#[derive(Clone)]
pub struct CorrectDecoderConfig<const W: usize = 4> {
    inp: Column<Advice>,
    out: [Column<Advice>; W],
    success: Column<Advice>,

    inp_instance: Column<Instance>,

    inv: [Column<Advice>; W],

    s: [Selector; W],
    s_success: Selector,
}

pub struct CorrectDecoderCircuit<F: PrimeField, const W: usize = 4>(pub PhantomData<F>);

impl<F: PrimeField, const W: usize> Default for CorrectDecoderCircuit<F, W> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<F: PrimeField, const W: usize> Circuit<F> for CorrectDecoderCircuit<F, W> {
    type Config = CorrectDecoderConfig<W>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self(PhantomData)
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> CorrectDecoderConfig<W> {
        let inp = meta.advice_column();
        let out = std::array::from_fn(|_| meta.advice_column());
        let success = meta.advice_column();

        let inp_instance = meta.instance_column();

        let inv = std::array::from_fn(|_| meta.advice_column());

        meta.enable_equality(inp);
        meta.enable_equality(inp_instance);

        let s = std::array::from_fn(|_| meta.selector());
        let s_success = meta.selector();

        for i in 0..W {
            meta.create_gate("correct_decoder_is_zero", |meta| {
                let selector = meta.query_selector(s[i]);
                let inp_q = meta.query_advice(inp, Rotation::cur());
                let out_q = meta.query_advice(out[i], Rotation::cur());
                let inv_q = meta.query_advice(inv[i], Rotation::cur());

                let one = Expression::Constant(F::ONE);
                let i_const = Expression::Constant(F::from(i as u64));
                let x = inp_q - i_const;

                vec![
                    selector.clone()
                        * (out_q.clone() - (one.clone() - x.clone() * inv_q.clone())),
                    selector.clone() * x * out_q.clone(),
                    selector * out_q * inv_q,
                ]
            });
        }

        meta.create_gate("correct_decoder_success", |meta| {
            let selector = meta.query_selector(s_success);
            let success_q = meta.query_advice(success, Rotation::cur());

            let sum = (0..W).fold(Expression::Constant(F::ZERO), |acc, i| {
                acc + meta.query_advice(out[i], Rotation::cur())
            });

            vec![selector * (success_q - sum)]
        });

        CorrectDecoderConfig {
            inp,
            out,
            success,
            inp_instance,
            inv,
            s,
            s_success,
        }
    }

    fn synthesize(
        &self,
        config: CorrectDecoderConfig<W>,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let inp_index = 2usize;
        let inp_value = F::from(inp_index as u64);
        let success_value = if inp_index < W { F::ONE } else { F::ZERO };

        let inp_cell= layouter.assign_region(
            || "correct decoder",
            |mut region| {
                let inp_cell = region.assign_advice(
                    || "inp",
                    config.inp,
                    0,
                    || Value::known(inp_value),
                )?;

                for i in 0..W {
                    config.s[i].enable(&mut region, 0)?;
                }
                config.s_success.enable(&mut region, 0)?;

                for i in 0..W {
                    let out_value = if i == inp_index { F::ONE } else { F::ZERO };
                    let x = inp_value - F::from(i as u64);
                    let inv_value = if i == inp_index {
                        F::ZERO
                    } else {
                        x.invert().unwrap()
                    };

                    region.assign_advice(
                        || format!("out{}", i),
                        config.out[i],
                        0,
                        || Value::known(out_value),
                    )?;

                    region.assign_advice(
                        || format!("inv{}", i),
                        config.inv[i],
                        0,
                        || Value::known(inv_value),
                    )?;
                }

                region.assign_advice(
                    || "success",
                    config.success,
                    0,
                    || Value::known(success_value),
                )?;

                Ok(inp_cell)
            },
        )?;

        layouter.constrain_instance(inp_cell.cell(), config.inp_instance, 0)?;

        Ok(())
    }
}
