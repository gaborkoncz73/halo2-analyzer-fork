use std::collections::HashMap;
use std::str;

#[derive(Debug, PartialEq, Eq)]
pub enum Satisfiability {
    Satisfiable,
    Unsatisfiable,
}
use anyhow::{anyhow, Context, Result};
use regex::Regex;

#[derive(Debug)]
pub struct UnknownSolverResult;

impl std::fmt::Display for UnknownSolverResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SMT solver returned unknown; no satisfiability conclusion"
        )
    }
}

impl std::error::Error for UnknownSolverResult {}

/// Optional CVC5 diagnostic; a configured time limit alone is not evidence of a timeout.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SolverUnknownDetails {
    pub reason: Option<String>,
}

impl std::fmt::Display for SolverUnknownDetails {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Solver unknown reason: {:?}", self.reason)
    }
}

impl std::error::Error for SolverUnknownDetails {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FieldElement {
    pub order: String,
    pub element: String,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Variable {
    pub name: String,
    pub value: FieldElement,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ModelResult {
    pub sat: Satisfiability,
    pub result: HashMap<String, Variable>,
}
/// Parses a field element from a string representation.
///
/// This function parses a string representation of a field element and constructs a `FieldElement`
/// struct containing the element value and its order.
///
fn parse_field_element_from_string(value: &str) -> Result<FieldElement> {
    // Remove #f and split by "m" to get (field element, field prime).
    let mut elements = value[2..].split('m');
    let value_str = elements.next().context("Failed to parse smt result!")?;
    let order_str = elements.next().context("Failed to parse smt result!")?;
    Ok(FieldElement {
        order: order_str.to_owned(),
        element: value_str.to_owned(),
    })
}
/// Extracts the model response from the SMT solver output.
///
/// This function parses the SMT solver output and extracts the model response, including
/// the satisfiability and variable assignments.
pub fn extract_model_response(stream: String) -> Result<ModelResult> {
    let mut lines = stream.lines();
    // Initializing values
    let mut variables: HashMap<String, Variable> = HashMap::new();
    let mut first_line = lines.next().context("Failed to parse smt result!")?;
    let diagnostic = Regex::new(r"^\(incomplete ([A-Z_]+)\)$")?;
    let mut reason = None;
    while let Some(captures) = diagnostic.captures(first_line.trim()) {
        reason = Some(captures[1].to_string());
        first_line = lines
            .next()
            .context("Missing result after solver diagnostic")?;
    }
    if first_line.trim() == "sat" {
        let re = Regex::new(r"\(\((\S+)\s+(\S+)\)\)").context("Failed to compile regex!")?;
        for line in lines {
            let trimmed_line = line.trim();
            if trimmed_line.is_empty() {
                continue;
            }
            if let Some(captures) = re.captures(trimmed_line) {
                if captures.len() < 3 {
                    return Err(anyhow::anyhow!("Failed to parse smt result!"));
                }
                let variable_name = captures
                    .get(1)
                    .map(|m| m.as_str())
                    .context("Failed to extract variable name!")?;
                let ff_element_string = captures
                    .get(2)
                    .map(|m| m.as_str())
                    .context("Failed to extract ff element!")?;
                let ff_element = parse_field_element_from_string(ff_element_string)
                    .context("Error in parsing model!")?;
                let variable = Variable {
                    name: variable_name.to_owned(),
                    value: ff_element,
                };
                variables.insert(variable_name.to_owned(), variable);
            }
        }
        Ok(ModelResult {
            sat: Satisfiability::Satisfiable,
            result: variables,
        })
    } else if first_line.trim() == "unsat" {
        Ok(ModelResult {
            sat: Satisfiability::Unsatisfiable,
            result: variables,
        })
    } else if first_line.trim() == "unknown" {
        Err(anyhow!(UnknownSolverResult).context(SolverUnknownDetails { reason }))
    } else {
        Err(anyhow!("SMT Solver Error: {}", first_line.trim()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unknown_is_a_distinct_error_not_sat_or_unsat() {
        let error = extract_model_response("unknown\n(error \"no model\")\n".into()).unwrap_err();
        assert!(error.downcast_ref::<UnknownSolverResult>().is_some());
        assert!(extract_model_response("invalid\n".into())
            .unwrap_err()
            .downcast_ref::<UnknownSolverResult>()
            .is_none());
    }

    #[test]
    fn incomplete_diagnostics_preserve_unknown_reason() {
        for reason in ["TIMEOUT", "RESOURCEOUT", "INCOMPLETE"] {
            let error =
                extract_model_response(format!("(incomplete {reason})\nunknown\n")).unwrap_err();
            assert!(error.downcast_ref::<UnknownSolverResult>().is_some());
            assert_eq!(
                error
                    .downcast_ref::<SolverUnknownDetails>()
                    .unwrap()
                    .reason
                    .as_deref(),
                Some(reason)
            );
        }
        let unspecified = extract_model_response("unknown\n".into()).unwrap_err();
        assert_eq!(
            unspecified
                .downcast_ref::<SolverUnknownDetails>()
                .unwrap()
                .reason,
            None
        );
        assert!(extract_model_response("(incomplete TIMEOUT)\n".into()).is_err());
    }
}
