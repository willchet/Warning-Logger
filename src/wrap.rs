use std::fmt::Display;

use crate::{AtomicWarning, Logger, Warning};

/// An extension trait allowing any value to be wrapped into a [`Logger`].
pub trait LoggingWrap: Sized {
    /// Wraps the value in a [`Logger`] with no warnings.
    #[inline]
    #[must_use]
    fn wrap<W: Warning>(self) -> Logger<Self, W> {
        Logger::new(self)
    }

    #[inline]
    #[must_use]
    fn wrap_basic(self) -> Logger<Self> {
        Logger::new(self)
    }

    /// Wraps the value in a [`Logger`] with no warnings.
    #[inline]
    #[must_use]
    fn wrap_atomic(self) -> Logger<Self, AtomicWarning> {
        Logger::new(self)
    }

    /// Wraps the value in a [`Logger`] with a set of warnings.
    #[inline]
    #[must_use]
    fn wrap_with_warnings<W: Warning, V: Warning>(
        self,
        warnings: Logger<(), V>,
    ) -> Logger<Self, W> {
        Logger {
            value: self,
            warnings: Warning::new_with(warnings.warnings.take_vec()),
        }
    }

    /// Wraps the value in a [`Logger`] with a set of warnings.
    #[inline]
    #[must_use]
    fn wrap_with_warnings_basic<W: Warning>(self, warnings: Logger<(), W>) -> Logger<Self> {
        Logger {
            value: self,
            warnings: Warning::new_with(warnings.warnings.take_vec()),
        }
    }

    /// Wraps the value in a [`Logger`] with a set of warnings.
    #[inline]
    #[must_use]
    fn wrap_with_warnings_atomic<W: Warning>(
        self,
        warnings: Logger<(), W>,
    ) -> Logger<Self, AtomicWarning> {
        Logger {
            value: self,
            warnings: Warning::new_with(warnings.warnings.take_vec()),
        }
    }

    /// Wraps the value in a [`Logger`] with a set of warnings and a context.
    /// The warnings appear indented beneath the context.
    #[inline]
    #[must_use]
    fn wrap_with_context<C: Display, W: Warning, V: Warning>(
        self,
        context: impl FnOnce() -> C,
        warnings: Logger<(), V>,
    ) -> Logger<Self, W> {
        let warnings = warnings.with_context(context).warnings;
        Logger {
            value: self,
            warnings: Warning::new_with(warnings.take_vec()),
        }
    }

    #[inline]
    #[must_use]
    fn wrap_with_context_basic<C: Display, W: Warning>(
        self,
        context: impl FnOnce() -> C,
        warnings: Logger<(), W>,
    ) -> Logger<Self> {
        let warnings = warnings.with_context(context).warnings;
        Logger {
            value: self,
            warnings: Warning::new_with(warnings.take_vec()),
        }
    }

    /// Wraps the value in a [`Logger`] with a set of warnings and a context.
    /// The warnings appear indented beneath the context.
    #[inline]
    #[must_use]
    fn wrap_with_context_atomic<C: Display, W: Warning>(
        self,
        context: impl FnOnce() -> C,
        warnings: Logger<(), W>,
    ) -> Logger<Self, AtomicWarning> {
        let warnings = warnings.with_context(context).warnings;
        Logger {
            value: self,
            warnings: Warning::new_with(warnings.take_vec()),
        }
    }
}

impl<T> LoggingWrap for T {}
