//! A tenyleges recovery fociklus fuggosegmentes vezerlese.
//! A muveleteket az eles adapter hajtja vegre; a sorrendet es az ujrainditast ez a modul donti el.

pub(crate) enum Selection<Action, Stop> {
    Run(Action),
    Stop(Stop),
}

// A tulajdonjog atadasa mozgatja az allapotot; nem masolja a domaineket vagy a solvert.
pub(crate) trait RecoveryMachine: Sized {
    type Action;
    type Pending;
    type Stop;
    type Error;

    fn propagate(self) -> Result<(Self, bool), Self::Error>;
    fn refresh(self) -> Result<Self, Self::Error>;
    fn select(self) -> Result<(Self, Selection<Self::Action, Self::Stop>), Self::Error>;
    fn query(self, action: Self::Action) -> Result<(Self, Self::Pending), Self::Error>;
    fn merge(self, pending: Self::Pending) -> Result<(Self, bool), Self::Error>;
}

// A kanonizalas uj domainte csak valodi valtozasnal ker meg egy propagacios kort.
fn propagate_until_stable<M: RecoveryMachine>(mut machine: M) -> Result<M, M::Error> {
    loop {
        let (next, repeat) = machine.propagate()?;
        machine = next;
        if !repeat {
            return machine.refresh();
        }
    }
}

// Nem jelol sikeresnek hibas muveletet, es minden keresesi eredmenyt beolvaszt a kovetkezo valasztas elott.
pub(crate) fn run_recovery<M: RecoveryMachine>(mut machine: M) -> Result<(M::Stop, M), M::Error> {
    let mut propagation_needed = true;
    loop {
        if propagation_needed {
            machine = propagate_until_stable(machine)?;
        }
        let (next, selection) = machine.select()?;
        machine = next;
        match selection {
            Selection::Stop(status) => return Ok((status, machine)),
            Selection::Run(action) => {
                let (next, pending) = machine.query(action)?;
                let (next, changed) = next.merge(pending)?;
                machine = next;
                propagation_needed = changed;
            }
        }
    }
}

#[cfg(test)]
#[path = "tests/recovery_loop_tests.rs"]
mod tests;
