//! Opcionális, szálhoz kötött időmérést végez a következtetési és keresési fázisokon.
//! A beágyazott mérések ideje átfedhet; az összege nem teljes futásidő.

use std::{
    cell::RefCell,
    collections::BTreeMap,
    fmt,
    time::{Duration, Instant},
};

#[derive(Clone, Debug, Default)]
pub struct Measurement {
    pub calls: usize,
    pub elapsed: Duration,
}

#[derive(Clone, Debug, Default)]
pub struct Profile {
    pub measurements: BTreeMap<&'static str, Measurement>,
    pub counters: BTreeMap<&'static str, usize>,
}

thread_local! {
    static ACTIVE: RefCell<Option<Profile>> = const { RefCell::new(None) };
}

// A munkamenet végén visszaállítja a külső mérést, így egymásba ágyazva is használható.
pub struct ProfilingSession {
    previous: Option<Profile>,
    _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl ProfilingSession {
    pub fn start() -> Self {
        Self {
            previous: ACTIVE.with(|active| active.replace(Some(Profile::default()))),
            _thread: std::marker::PhantomData,
        }
    }

    pub fn snapshot(&self) -> Profile {
        ACTIVE.with(|active| active.borrow().clone().unwrap_or_default())
    }
}

impl Drop for ProfilingSession {
    fn drop(&mut self) {
        ACTIVE.with(|active| {
            active.replace(self.previous.take());
        });
    }
}

pub(crate) struct Timer {
    name: &'static str,
    started: Option<Instant>,
}

pub(crate) fn scope(name: &'static str) -> Timer {
    Timer {
        name,
        started: ACTIVE.with(|active| active.borrow().as_ref().map(|_| Instant::now())),
    }
}

pub(crate) fn count(name: &'static str) {
    ACTIVE.with(|active| {
        if let Some(profile) = active.borrow_mut().as_mut() {
            *profile.counters.entry(name).or_default() += 1;
        }
    });
}

impl Drop for Timer {
    fn drop(&mut self) {
        if let Some(started) = self.started {
            let elapsed = started.elapsed();
            ACTIVE.with(|active| {
                if let Some(profile) = active.borrow_mut().as_mut() {
                    let measurement = profile.measurements.entry(self.name).or_default();
                    measurement.calls += 1;
                    measurement.elapsed += elapsed;
                }
            });
        }
    }
}

impl fmt::Display for Profile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, measurement) in &self.measurements {
            writeln!(
                f,
                "PROFILE phase={name} calls={} elapsed_ms={:.3}",
                measurement.calls,
                measurement.elapsed.as_secs_f64() * 1000.0
            )?;
        }
        for (name, value) in &self.counters {
            writeln!(f, "PROFILE counter={name} value={value}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profiling_is_scoped_and_nested_sessions_are_isolated() {
        let outer = ProfilingSession::start();
        {
            let _timer = scope("outer");
        }
        {
            let inner = ProfilingSession::start();
            count("inner");
            assert_eq!(inner.snapshot().counters["inner"], 1);
            assert!(inner.snapshot().measurements.is_empty());
        }
        assert_eq!(outer.snapshot().measurements["outer"].calls, 1);
        assert!(outer.snapshot().counters.is_empty());
    }
}
