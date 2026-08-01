//! Context-free parsing with Earley item sets plus precedence and gather constraints.
//!
//! Items use the typed grammar symbols from [`grammar`](crate::grammar). A finished production of
//! precedence `p` may advance a waiting item over a hole exactly when that hole's gather bound is at
//! least `p`. Earley prediction handles left recursion; each caller's maximum precedence is enforced
//! by its containing hole when that production completes.

pub mod compile;
pub mod earley;
pub mod forest;

/// Deterministic work allowed for one complete recognizer + forest-extraction pass. The threshold is
/// deliberately expressed in parser operations rather than elapsed time so identical input fails at the
/// same token on every host.
pub const DEFAULT_PARSE_EFFORT_LIMIT: u64 = 100_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EffortExceeded {
    pub at: usize,
}

/// Shared operation budget for both Earley passes. Each prediction visit, scanner check, completion
/// candidate check, and forest candidate/node visit consumes one unit.
#[derive(Debug)]
pub struct ParseEffort {
    remaining: u64,
    #[cfg(test)]
    used: u64,
}

impl Default for ParseEffort {
    fn default() -> Self {
        Self::new(DEFAULT_PARSE_EFFORT_LIMIT)
    }
}

impl ParseEffort {
    pub fn new(limit: u64) -> Self {
        Self {
            remaining: limit,
            #[cfg(test)]
            used: 0,
        }
    }

    #[cfg(test)]
    pub(crate) fn used(&self) -> u64 {
        self.used
    }

    pub(crate) fn charge(&mut self, at: usize) -> Result<(), EffortExceeded> {
        if self.remaining == 0 {
            return Err(EffortExceeded { at });
        }
        self.remaining -= 1;
        #[cfg(test)]
        {
            self.used += 1;
        }
        Ok(())
    }

    pub(crate) fn charge_many(&mut self, amount: usize, at: usize) -> Result<(), EffortExceeded> {
        let amount = amount as u64;
        if self.remaining < amount {
            #[cfg(test)]
            {
                self.used += self.remaining;
            }
            self.remaining = 0;
            return Err(EffortExceeded { at });
        }
        self.remaining -= amount;
        #[cfg(test)]
        {
            self.used += amount;
        }
        Ok(())
    }
}
