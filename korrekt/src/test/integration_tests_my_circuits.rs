#[cfg(test)]
#[cfg(feature = "use_zcash_halo2_proofs")]
mod tests {
    use crate::circuit_analyzer::analyzer::Analyzer;
    use crate::io::analyzer_io_type::AnalyzerType;
    use crate::io::{
        analyzer_io_type,
        analyzer_io_type::{
            AnalyzerOutputStatus, LookupMethod, VerificationInput, VerificationMethod,
        },
    };
    use std::collections::HashMap;
    use std::marker::PhantomData;
    use zcash_halo2_proofs::pasta::Fp as Fr;

    #[test]
    fn test_underconstrained_decoder_detected() {
        use crate::sample_circuits::zcash::simple::decoder_circuits::UnderDecoderCircuit;
        let circuit = UnderDecoderCircuit::<Fr, 8>(PhantomData);
        let k: u32 = 5;
        let mut instance_cells = HashMap::new();
        instance_cells.insert("I-0-0".to_string(), 2);
        let analyzer_input = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instance_cells,
                iterations: 5,
            },
            lookup_method: LookupMethod::InlineConstraints,
        };
        let mut analyzer = Analyzer::new(
            &circuit,
            k,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&analyzer_input),
        )
        .unwrap();
        let output_status = analyzer
            .analyze_underconstrained(&analyzer_input)
            .unwrap()
            .output_status;
        println!("Underconstrained decoder: {:?}", output_status);
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    use zcash_halo2_proofs::dev::MockProver;

    #[test]
    fn test_under_decoder_witness_is_satisfied() {
        use crate::sample_circuits::zcash::simple::decoder_circuits::UnderDecoderCircuit;

        let circuit = UnderDecoderCircuit::<Fr>(PhantomData);
        let k: u32 = 5;
        let public_inputs = vec![vec![Fr::from(2u64)]];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();

        prover.assert_satisfied();
    }

    #[test]
    fn test_correct_decoder_not_underconstrained() {
        use crate::sample_circuits::zcash::simple::decoder_circuits::CorrectDecoderCircuit;

        let circuit = CorrectDecoderCircuit::<Fr, 8>(PhantomData);
        let k: u32 = 5;

        let mut instance_cells = HashMap::new();
        instance_cells.insert("I-0-0".to_string(), 2);

        let analyzer_input = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instance_cells,
                iterations: 7,
            },
            lookup_method: LookupMethod::InlineConstraints,
        };

        let mut analyzer = Analyzer::new(
            &circuit,
            k,
            AnalyzerType::UnderconstrainedCircuit,
            Some(&analyzer_input),
        )
        .unwrap();

        let output_status = analyzer
            .analyze_underconstrained(&analyzer_input)
            .unwrap()
            .output_status;

        println!("Helyes decoder: {:?}", output_status);

        assert!(
            output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal)
                || output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained)
        );
    }

    #[test]
    fn test_correct_decoder_witness_is_satisfied() {
        use crate::sample_circuits::zcash::simple::decoder_circuits::CorrectDecoderCircuit;

        let circuit = CorrectDecoderCircuit::<Fr>(PhantomData);
        let k: u32 = 5;

        let public_inputs = vec![vec![Fr::from(2u64)]];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();

        prover.assert_satisfied();
    }
}
