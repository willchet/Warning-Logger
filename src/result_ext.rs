use crate::{Logger, Warning, warning_with_context};
use anyhow::{Result, anyhow};
use std::fmt::Display;

/// An extension trait for `Result`.
pub trait ResultExt {
    type T;

    /// Applies a context to a given error. The error becomes indented beneath
    /// the context.
    fn err_with_context<C: Display>(self, context: impl FnOnce() -> C) -> Result<Self::T>;

    fn log_error<S, W: Warning>(self, logger: &Logger<S, W>);
}

impl<T, E: Display> ResultExt for Result<T, E> {
    type T = T;

    #[inline]
    fn err_with_context<C: Display>(self, context: impl FnOnce() -> C) -> Result<Self::T> {
        self.map_err(|e| anyhow!(warning_with_context(e, context)))
    }

    #[inline]
    fn log_error<S, W: Warning>(self, logger: &Logger<S, W>) {
        if let Err(e) = self {
            logger.log(e)
        }
    }
}
