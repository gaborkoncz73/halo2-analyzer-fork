//! Supervises one solver invocation; late or partial output cannot become a proof.
use super::smt_parser::{SolverUnknownDetails, UnknownSolverResult};
use anyhow::{anyhow, Context, Result};
use std::{
    io::Read,
    process::{Child, Command, ExitStatus, Output, Stdio},
    thread,
    time::{Duration, Instant},
};

pub(crate) const WALLCLOCK_TIMEOUT_REASON: &str = "WALLCLOCK_TIMEOUT";

thread_local! {
    static INVOCATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn invocation_count() -> usize {
    INVOCATIONS.with(|count| count.get())
}

struct ManagedChild(Child);

impl Drop for ManagedChild {
    fn drop(&mut self) {
        if !matches!(self.0.try_wait(), Ok(Some(_))) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
}

pub(crate) fn run(mut command: Command, budget: Option<Duration>) -> Result<Output> {
    let _profile = crate::circuit_analyzer::ucp::profiling::scope("smt.process");
    let Some(budget) = budget else {
        let output = command.output().context("Failed to execute solver");
        if output.is_ok() {
            INVOCATIONS.with(|count| count.set(count.get() + 1));
        }
        return output;
    };
    if budget.is_zero() {
        return Err(anyhow!("Solver process budget must be greater than zero"));
    }
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    let started = Instant::now();
    let mut child = ManagedChild(command.spawn().context("Failed to start solver")?);
    INVOCATIONS.with(|count| count.set(count.get() + 1));
    let stdout = child
        .0
        .stdout
        .take()
        .context("Solver stdout is unavailable")?;
    let stderr = child
        .0
        .stderr
        .take()
        .context("Solver stderr is unavailable")?;
    //Drain both pipes concurrently: a verbose solver must not deadlock the supervisor.
    let stdout = thread::spawn(move || read_output(stdout));
    let stderr = thread::spawn(move || read_output(stderr));
    let result = wait(&mut child.0, started, budget);
    if result.is_err() {
        //Reap before joining readers. No partial model is returned on a deadline.
        let _ = child.0.kill();
        let _ = child.0.wait();
    }
    let stdout = stdout
        .join()
        .map_err(|_| anyhow!("Solver stdout reader panicked"))?;
    let stderr = stderr
        .join()
        .map_err(|_| anyhow!("Solver stderr reader panicked"))?;
    let status = result?;
    Ok(Output {
        status,
        stdout: stdout.context("Failed to read solver stdout")?,
        stderr: stderr.context("Failed to read solver stderr")?,
    })
}

fn wait(child: &mut Child, started: Instant, budget: Duration) -> Result<ExitStatus> {
    loop {
        if started.elapsed() >= budget {
            return Err(anyhow!(UnknownSolverResult).context(SolverUnknownDetails {
                reason: Some(WALLCLOCK_TIMEOUT_REASON.into()),
            }));
        }
        if let Some(status) = child.try_wait().context("Failed to poll solver process")? {
            return Ok(status);
        }
        thread::sleep(Duration::from_millis(2).min(budget.saturating_sub(started.elapsed())));
    }
}

fn read_output(mut pipe: impl Read) -> std::io::Result<Vec<u8>> {
    let mut output = Vec::new();
    pipe.read_to_end(&mut output)?;
    Ok(output)
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn shell(script: &str) -> Command {
        let mut command = Command::new("/bin/sh");
        command.args(["-c", script]);
        command
    }

    #[test]
    fn deadline_kills_solver_and_discards_partial_sat_output() {
        let started = Instant::now();
        let error = run(
            shell("printf 'sat\\n'; exec sleep 5"),
            Some(Duration::from_millis(100)),
        )
        .unwrap_err();
        assert!(error.downcast_ref::<UnknownSolverResult>().is_some());
        assert_eq!(
            error
                .downcast_ref::<SolverUnknownDetails>()
                .unwrap()
                .reason
                .as_deref(),
            Some(WALLCLOCK_TIMEOUT_REASON)
        );
        assert!(started.elapsed() < Duration::from_secs(2));
    }

    #[test]
    fn successful_process_retains_both_output_streams() {
        let output = run(
            shell("printf 'sat\\n'; printf 'diagnostic' >&2"),
            Some(Duration::from_secs(2)),
        )
        .unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, b"sat\n");
        assert_eq!(output.stderr, b"diagnostic");
    }

    #[test]
    fn readers_drain_output_larger_than_pipe_capacity() {
        let output = run(
            shell("head -c 200000 /dev/zero; head -c 200000 /dev/zero >&2"),
            Some(Duration::from_secs(2)),
        )
        .unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout.len(), 200000);
        assert_eq!(output.stderr.len(), 200000);
    }

    #[test]
    fn zero_budget_is_rejected_without_starting_the_process() {
        assert!(run(shell("exit 0"), Some(Duration::ZERO)).is_err());
    }

    #[test]
    fn missing_solver_is_an_execution_error_not_a_timeout() {
        let error = run(
            Command::new("/no/such/solver"),
            Some(Duration::from_secs(1)),
        )
        .unwrap_err();
        assert!(error.downcast_ref::<UnknownSolverResult>().is_none());
    }
}
