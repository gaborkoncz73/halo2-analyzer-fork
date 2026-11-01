use super::{run_recovery, RecoveryMachine, Selection};
use std::collections::VecDeque;

struct Script {
    trace: Vec<&'static str>,
    changed: VecDeque<bool>,
    repeats: VecDeque<bool>,
    fail_at: Option<&'static str>,
}

impl Script {
    fn record(&mut self, stage: &'static str) -> Result<(), &'static str> {
        self.trace.push(stage);
        if self.fail_at == Some(stage) {
            Err(stage)
        } else {
            Ok(())
        }
    }
}

impl RecoveryMachine for Script {
    type Action = ();
    type Pending = bool;
    type Stop = ();
    type Error = &'static str;

    fn propagate(mut self) -> Result<(Self, bool), Self::Error> {
        self.record("ucp")?;
        let repeat = self.repeats.pop_front().unwrap_or(false);
        Ok((self, repeat))
    }

    fn refresh(mut self) -> Result<Self, Self::Error> {
        self.record("refresh")?;
        Ok(self)
    }

    fn select(mut self) -> Result<(Self, Selection<Self::Action, Self::Stop>), Self::Error> {
        self.record("select")?;
        let action = if self.changed.is_empty() {
            Selection::Stop(())
        } else {
            Selection::Run(())
        };
        Ok((self, action))
    }

    fn query(mut self, _: Self::Action) -> Result<(Self, Self::Pending), Self::Error> {
        self.record("query")?;
        let changed = self.changed.pop_front().unwrap();
        Ok((self, changed))
    }

    fn merge(mut self, changed: Self::Pending) -> Result<(Self, bool), Self::Error> {
        self.record("merge")?;
        Ok((self, changed))
    }
}

fn script(changed: &[bool], repeats: &[bool]) -> Script {
    Script {
        trace: Vec::new(),
        changed: changed.iter().copied().collect(),
        repeats: repeats.iter().copied().collect(),
        fail_at: None,
    }
}

#[test]
fn initial_propagation_precedes_selection() {
    let (_, result) = run_recovery(script(&[], &[])).unwrap();
    assert_eq!(result.trace, ["ucp", "refresh", "select"]);
}

#[test]
fn unchanged_evidence_does_not_restart_ucp() {
    let (_, result) = run_recovery(script(&[false, false], &[])).unwrap();
    assert_eq!(
        result.trace,
        ["ucp", "refresh", "select", "query", "merge", "select", "query", "merge", "select"]
    );
}

#[test]
fn learned_facts_restart_before_the_next_selection() {
    let (_, result) = run_recovery(script(&[true, false], &[])).unwrap();
    assert_eq!(
        result.trace,
        [
            "ucp", "refresh", "select", "query", "merge", "ucp", "refresh", "select", "query",
            "merge", "select"
        ]
    );
}

#[test]
fn canonicalization_repeats_propagation_before_refreshing_search_facts() {
    let (_, result) = run_recovery(script(&[], &[true, true, false])).unwrap();
    assert_eq!(result.trace, ["ucp", "ucp", "ucp", "refresh", "select"]);
}

#[test]
fn stage_errors_are_not_returned_as_success() {
    for stage in ["ucp", "refresh", "select", "query", "merge"] {
        let mut input = script(&[true], &[]);
        input.fail_at = Some(stage);
        assert!(matches!(run_recovery(input), Err(error) if error == stage));
    }
}
