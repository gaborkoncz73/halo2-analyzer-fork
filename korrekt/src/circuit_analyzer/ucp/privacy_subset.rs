//! Bounded selection of literal original equations using encoder-supplied variable metadata.
//! A selected conjunction is weaker than the original model, never a replacement for SAT evidence.

use std::collections::{BTreeMap, BTreeSet};

pub(crate) const MAX_ORIGINAL_RECOVERY_ASSERTIONS: usize = 4096;
pub(crate) const MAX_TARGETED_SUBSET_ASSERTIONS: usize = 64;
pub(crate) const MAX_TARGETED_SUBSET_DEPTH: usize = 2;
pub(crate) const PRIVACY_TARGETED_SUBSET_POLICY: &str = "literal-targeted-exclusion-unsat-only-v1";

#[derive(Clone, Debug)]
pub(crate) struct OriginalSmtAssertion {
    pub body: String,
    pub variables: BTreeSet<String>,
}

#[derive(Debug, Default)]
pub(crate) struct OriginalAssertionStore {
    pub assertions: Vec<OriginalSmtAssertion>,
}

impl OriginalAssertionStore {
    pub fn has_capacity(&self) -> bool {
        self.assertions.len() < MAX_ORIGINAL_RECOVERY_ASSERTIONS
    }

    pub fn retain(&mut self, body: String, variables: impl IntoIterator<Item = String>) {
        if self.has_capacity() {
            self.assertions.push(OriginalSmtAssertion {
                body,
                variables: variables.into_iter().collect(),
            });
        }
    }

    pub fn index(&self) -> BTreeMap<String, Vec<usize>> {
        let mut index = BTreeMap::<_, Vec<_>>::new();
        for (position, assertion) in self.assertions.iter().enumerate() {
            for variable in &assertion.variables {
                index.entry(variable.clone()).or_default().push(position);
            }
        }
        index
    }

    pub fn select<'a>(
        &'a self,
        target: &str,
        public_variables: &BTreeSet<String>,
        index: &BTreeMap<String, Vec<usize>>,
    ) -> Vec<&'a OriginalSmtAssertion> {
        let mut frontier = BTreeSet::from([target.to_owned()]);
        let mut visited = BTreeSet::new();
        let mut selected = BTreeSet::new();
        for _ in 0..MAX_TARGETED_SUBSET_DEPTH {
            let mut next = BTreeSet::new();
            for variable in frontier {
                if !visited.insert(variable.clone()) {
                    continue;
                }
                for &position in index.get(&variable).into_iter().flatten() {
                    if selected.len() >= MAX_TARGETED_SUBSET_ASSERTIONS {
                        break;
                    }
                    if selected.insert(position) {
                        // Concrete public observations are leaves, not connections to unrelated gates.
                        next.extend(
                            self.assertions[position]
                                .variables
                                .iter()
                                .filter(|name| {
                                    !public_variables.contains(*name) && !visited.contains(*name)
                                })
                                .cloned(),
                        );
                    }
                }
            }
            frontier = next;
        }
        selected
            .into_iter()
            .map(|position| &self.assertions[position])
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn retain(store: &mut OriginalAssertionStore, body: &str, variables: &[&str]) {
        store.retain(
            body.to_owned(),
            variables.iter().map(|name| (*name).to_owned()),
        );
    }

    #[test]
    fn selection_preserves_whole_equations_and_does_not_join_through_public_inputs() {
        let mut store = OriginalAssertionStore::default();
        retain(&mut store, "quadratic target equation", &["x", "I-0-0"]);
        retain(&mut store, "neighbor equation", &["x", "y"]);
        retain(&mut store, "second-hop equation", &["y", "z"]);
        retain(
            &mut store,
            "unrelated public-dependent equation",
            &["w", "I-0-0"],
        );
        retain(&mut store, "third-hop equation", &["z", "a"]);
        let index = store.index();
        let selected = store.select("x", &BTreeSet::from(["I-0-0".to_owned()]), &index);
        assert_eq!(
            selected
                .iter()
                .map(|assertion| assertion.body.as_str())
                .collect::<Vec<_>>(),
            vec![
                "quadratic target equation",
                "neighbor equation",
                "second-hop equation"
            ]
        );
        assert_eq!(
            selected[0].variables,
            BTreeSet::from(["x".to_owned(), "I-0-0".to_owned()])
        );
    }

    #[test]
    fn selection_uses_exact_variable_names_and_has_no_implicit_global_constraints() {
        let mut store = OriginalAssertionStore::default();
        retain(&mut store, "first", &["A-1-0"]);
        retain(&mut store, "different symbol", &["A-10-0"]);
        retain(&mut store, "constant contradiction", &[]);
        let index = store.index();
        assert_eq!(store.select("A-1-0", &BTreeSet::new(), &index).len(), 1);
        assert!(store.select("missing", &BTreeSet::new(), &index).is_empty());
    }

    #[test]
    fn limits_omit_entire_assertions_without_altering_retained_bodies() {
        let mut store = OriginalAssertionStore::default();
        for position in 0..=MAX_ORIGINAL_RECOVERY_ASSERTIONS {
            store.retain(format!("literal-{position}"), ["x".to_owned()]);
        }
        assert_eq!(store.assertions.len(), MAX_ORIGINAL_RECOVERY_ASSERTIONS);
        let selected = store.select("x", &BTreeSet::new(), &store.index());
        assert_eq!(selected.len(), MAX_TARGETED_SUBSET_ASSERTIONS);
        for (position, assertion) in selected.into_iter().enumerate() {
            assert_eq!(assertion.body, format!("literal-{position}"));
        }
    }
}
