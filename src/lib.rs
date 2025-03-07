#![feature(iter_intersperse, let_chains, min_specialization)]

use anyhow::{Result, anyhow};
use std::{
    cell::RefCell,
    fmt::Display,
    iter::{FilterMap, Map},
    rc::Rc,
};

#[macro_export]
macro_rules! context {
    ($msg:expr) => {
        || format!($msg)
    };
    ($fmt:expr, $($arg:tt)*) => {
        || format!($fmt, $($arg)*)
    };
}

/// Apply a context to a given warning. The warning becomes indented beneath the
/// context.
#[inline]
fn warning_with_context<E: Display, C: Display>(warning: E, context: impl FnOnce() -> C) -> String {
    format!(
        "{}\n|    {}",
        context(),
        &warning.to_string().replace('\n', "\n|    ")
    )
}

/// Print a warning with a given context applied. The warning becomes indented
/// beneath the context.
#[inline]
fn print_warning_with_context<E: Display, C: Display>(warning: E, context: impl FnOnce() -> C) {
    eprintln!("{}", warning_with_context(warning, context));
}

/// A struct wrapping any type which also holds any number of warnings.
#[derive(Debug)]
pub struct Logger<T> {
    value: T,
    warnings: Rc<RefCell<Vec<String>>>,
}

impl<T, E> Logger<Result<T, E>> {
    /// Converts a [`Logger`] of a [`Result`] to a [`Result`] of a [`Logger`].
    #[inline]
    pub fn transpose(self) -> Result<Logger<T>, E> {
        Ok(Logger {
            value: self.value?,
            warnings: self.warnings,
        })
    }
}

impl<T> Logger<T> {
    /// Wraps an existing value in a [`Logger`] with no warnings.
    #[inline]
    pub fn new(value: T) -> Self {
        Self {
            value,
            warnings: Rc::new(RefCell::new(vec![])),
        }
    }

    /// Retrieves a reference to the value stored in the [`Logger`].
    #[inline]
    pub fn val(&self) -> &T {
        &self.value
    }

    /// Retrieves a mutable reference to the value stored in the [`Logger`].
    #[inline]
    pub fn val_mut(&mut self) -> &mut T {
        &mut self.value
    }

    /// Returns whether any warnings are being stored by the [`Logger`].
    #[inline]
    pub fn has_warning(&self) -> bool {
        !self.warnings.borrow().is_empty()
    }

    /// Adds a warning to the [`Logger`].
    #[inline]
    pub fn log(&self, warning: impl Display) {
        self.warnings.borrow_mut().push(warning.to_string());
    }

    /// Adds a warning to the [`Logger`] with a context applied. The warning
    /// appears indented beneath the context.
    #[inline]
    pub fn log_with_context<C: Display>(&self, warning: impl Display, context: impl FnOnce() -> C) {
        self.log(warning_with_context(warning, context));
    }

    /// Transforms the value stored in the [`Logger`].
    #[inline]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Logger<U> {
        Logger {
            value: f(self.value),
            warnings: self.warnings,
        }
    }

    /// Applies a context to the currently logged warnings. The warnings appear
    /// indented beneath the context.
    #[inline]
    pub fn with_context<C: Display>(mut self, context: impl FnOnce() -> C) -> Self {
        if let Some(warning) = self.with_context_helper(context) {
            self.warnings = Rc::new(RefCell::new(vec![warning]));
        }
        self
    }

    /// Unwraps the value of a logger, taking its warnings and logging them in a
    /// new logger.
    #[inline]
    pub fn relog<S>(self, logger: &Logger<S>) -> T {
        for warning in self.warnings.borrow().iter() {
            logger.log(warning);
        }
        self.value
    }

    /// Unwraps the value of a log, taking its warnings and logging them in a
    /// new log with a context applied. The warnings appear indented beneath
    /// the context.
    #[inline]
    pub fn relog_with_context<S, C: Display>(
        self,
        context: impl FnOnce() -> C,
        logger: &Logger<S>,
    ) -> T {
        if let Some(warning) = self.with_context_helper(context) {
            logger.log(warning)
        }
        self.value
    }

    /// Unwraps the value of a log, printing its warnings.
    #[inline]
    pub fn print_warnings(self) -> T {
        for warning in self.warnings.borrow().iter() {
            eprintln!("{warning}");
        }
        self.value
    }

    /// Unwraps the value of a log, printing its warnings with a context
    /// applied. The warnings appear indented beneath the context.
    #[inline]
    pub fn print_warnings_with_context<C: Display>(self, context: impl FnOnce() -> C) -> T {
        if let Some(warning) = self.with_context_helper(context) {
            eprintln!("{warning}");
        }
        self.value
    }

    /// Retrieves the warnings with a context applied. The warnings appear
    /// indented beneath the context. If no warnings are present, then `None` is
    /// returned.
    #[inline]
    fn with_context_helper<C: Display>(&self, context: impl FnOnce() -> C) -> Option<String> {
        self.has_warning().then(|| {
            context().to_string()
                + "\n|    "
                + &self
                    .warnings
                    .borrow()
                    .iter()
                    .map(|x| x.replace('\n', "\n|    "))
                    .intersperse("\n|    ".to_string())
                    .collect::<String>()
        })
    }
}

/// An extension trait for a result containing a [`Logger`] (i.e., a value
/// wrapped with both warnings and a potential error).
pub trait LoggerInResult<T, E> {
    /// Applies a context to the [`Logger`], if there is no error. The warnings
    /// appear indented beneath the context.
    #[must_use]
    fn warnings_with_context<C: Display>(self, context: impl FnOnce() -> C) -> Self;

    /// Transforms the value stored in the [`Logger`] within the [`Result`].
    fn map_val<U>(self, f: impl FnOnce(T) -> U) -> Result<Logger<U>, E>;
}

impl<T, E> LoggerInResult<T, E> for Result<Logger<T>, E> {
    #[inline]
    fn warnings_with_context<C: Display>(mut self, context: impl FnOnce() -> C) -> Self {
        if let Ok(log) = &mut self
            && let Some(warning) = log.with_context_helper(context)
        {
            log.warnings = Rc::new(RefCell::new(vec![warning]));
        }
        self
    }

    #[inline]
    fn map_val<U>(self, f: impl FnOnce(T) -> U) -> Result<Logger<U>, E> {
        self.map(|log| Logger {
            value: f(log.value),
            warnings: log.warnings,
        })
    }
}

/// An extension trait allowing any value to be wrapped into a [`Logger`].
pub trait LoggingWrap: Sized {
    /// Wraps the value in a [`Logger`] with no warnings.
    #[inline]
    #[must_use]
    fn wrap(self) -> Logger<Self> {
        Logger::new(self)
    }

    /// Wraps the value in a [`Logger`] with a set of warnings.
    #[inline]
    #[must_use]
    fn wrap_with_warnings(self, warnings: Logger<()>) -> Logger<Self> {
        Logger {
            value: self,
            warnings: warnings.warnings,
        }
    }

    /// Wraps the value in a [`Logger`] with a set of warnings and a context.
    /// The warnings appear indented beneath the context.
    #[inline]
    #[must_use]
    fn wrap_with_context<C: Display>(
        self,
        context: impl FnOnce() -> C,
        warnings: Logger<()>,
    ) -> Logger<Self> {
        let warnings = warnings.with_context(context).warnings;
        Logger {
            value: self,
            warnings,
        }
    }
}

impl<T> LoggingWrap for T {}

/// An extension trait providing the ability to apply a context to a `Result`
/// (similar to a [`Logger`]).
pub trait ResultContext {
    type T;

    /// Applies a context to a given error. The error becomes indented beneath
    /// the context.
    fn err_with_context<C: Display>(self, context: impl FnOnce() -> C) -> Result<Self::T>;
}

impl<T, E: Display> ResultContext for Result<T, E> {
    type T = T;

    #[inline]
    fn err_with_context<C: Display>(self, context: impl FnOnce() -> C) -> Result<Self::T> {
        self.map_err(|e| anyhow!(warning_with_context(e, context)))
    }
}

/// An extension trait for iterators whose items are results. It provides the
/// ability to filter errors from the iterator and record them as warnings.
pub trait LogErrors: Iterator {
    /// Filters the errors from an iterator of results, logging them as warnings
    /// to `log`.
    #[inline]
    fn log_errors<S, T, E: Display>(
        self,
        logger: &Logger<S>,
    ) -> FilterMap<Self, impl FnMut(Result<T, E>) -> Option<T>>
    where
        Self: Sized + Iterator<Item = Result<T, E>>,
    {
        self.into_iter().filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(e) => {
                (*logger).log(e);
                None
            }
        })
    }

    /// Filters the errors from an iterator of results, logging each as a
    /// warning saying `message`.
    #[inline]
    fn log_errors_with_message<S, T, E>(
        self,
        logger: &Logger<S>,
        message: String,
    ) -> FilterMap<Self, impl FnMut(Result<T, E>) -> Option<T>>
    where
        Self: Sized + Iterator<Item = Result<T, E>>,
    {
        self.into_iter().filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(_) => {
                (*logger).log(message.clone());
                None
            }
        })
    }

    /// Filters the errors from an iterator of results, logging them as warnings
    /// to `log` with a context applied. The warnings appear indented beneath
    /// the context.
    #[inline]
    fn log_errors_with_context<'a, S, T, E: Display, C: Display>(
        self,
        logger: &'a Logger<S>,
        context: impl Fn() -> C,
    ) -> FilterMap<Self, impl FnMut(Result<T, E>) -> Option<T>>
    where
        Self: Sized + Iterator<Item = Result<T, E>>,
        for<'b> &'b C: Copy,
    {
        self.into_iter().filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(e) => {
                logger.log_with_context(e, &context);
                None
            }
        })
    }

    /// Filters the errors from an iterator of results, printing them.
    #[inline]
    fn print_errors<T, E: Display>(self) -> FilterMap<Self, impl FnMut(Result<T, E>) -> Option<T>>
    where
        Self: Sized + Iterator<Item = Result<T, E>>,
    {
        self.into_iter().filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(e) => {
                eprintln!("{e}");
                None
            }
        })
    }

    /// Filters the errors from an iterator of results, printing them with a
    /// context applied. The warnings appear indented beneath the context.
    #[inline]
    fn print_errors_with_context<T, E: Display, C: Display>(
        self,
        context: impl Fn() -> C,
    ) -> FilterMap<Self, impl FnMut(Result<T, E>) -> Option<T>>
    where
        Self: Sized + Iterator<Item = Result<T, E>>,
    {
        self.into_iter().filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(e) => {
                print_warning_with_context(e, &context);
                None
            }
        })
    }
}

impl<I, T, E> LogErrors for I where I: Iterator<Item = Result<T, E>> {}

/// An extension trait for iterators whose items are loggers. It provides the
/// ability to unwrap the values in the iterator and relog the warnings.
pub trait LogWarnings: Iterator {
    /// Relogs all warnings in an iterator, unwrapping each [`Logger`].
    #[inline]
    fn log_warnings<S, T>(self, logger: &Logger<S>) -> Map<Self, impl FnMut(Logger<T>) -> T>
    where
        Self: Sized + Iterator<Item = Logger<T>>,
    {
        self.into_iter().map(move |item| item.relog(logger))
    }

    /// Relogs all warnings in an iterator with a context applied, unwrapping
    /// each [`Logger`]. The warnings appear indented beneath the context.
    #[inline]
    fn log_warnings_with_context<S, T, C: Display>(
        self,
        logger: &Logger<S>,
        context: impl Fn() -> C,
    ) -> Map<Self, impl FnMut(Logger<T>) -> T>
    where
        Self: Sized + Iterator<Item = Logger<T>>,
    {
        self.into_iter()
            .map(move |item| item.relog_with_context(&context, logger))
    }

    /// Prints all warnings in an iterator, unwrapping each [`Logger`].
    #[inline]
    fn print_warnings<T>(self) -> Map<Self, impl FnMut(Logger<T>) -> T>
    where
        Self: Sized + Iterator<Item = Logger<T>>,
    {
        self.into_iter().map(move |item| item.print_warnings())
    }
}

impl<I, T> LogWarnings for I where I: Iterator<Item = Logger<T>> {}

/// A fallible version of [`FromIterator`], where any item that fails generates
/// a warning in the [`Logger`].
pub trait FromIteratorWithWarnings<A>: Sized {
    /// Builds a collection from an iterator, where processing of each item may
    /// fail. Any failed items generate a warning in the [`Logger`].
    #[must_use]
    fn from_iter_with_warnings<T: IntoIterator<Item = A>>(iter: T) -> Logger<Self>;
}

/// A fallible version of [`collect`]. See [`FromIteratorWithWarnings`] for more
/// details.
///
/// [`collect`]: std::iter::Iterator::collect
pub trait CollectWithWarning<T>: Iterator<Item = T> {
    /// Builds a collection from an iterator, where processing of each item may
    /// fail. Any failed items generate a warning in the [`Logger`].
    #[inline]
    #[must_use]
    fn collect_with_warnings<B: FromIteratorWithWarnings<T>>(self) -> Logger<B>
    where
        Self: Sized,
    {
        FromIteratorWithWarnings::from_iter_with_warnings(self)
    }
}

impl<T, I: Iterator<Item = T>> CollectWithWarning<T> for I {}
