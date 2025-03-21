#![feature(iter_intersperse, let_chains)]

use anyhow::{Error, Result, anyhow};
use rayon::iter::ParallelIterator;
use std::{
    borrow::Borrow,
    fmt::Display,
    iter::{FilterMap, Map},
    sync::mpsc::Sender,
};

mod error_ext;
mod result_ext;
mod warning;
mod wrap;

pub use error_ext::*;
pub use result_ext::*;
pub use warning::*;
pub use wrap::*;

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
pub(crate) fn warning_with_context<E: Display, C: Display>(
    warning: E,
    context: impl FnOnce() -> C,
) -> String {
    format!(
        "{}\n|    {}",
        context(),
        &warning.to_string().replace('\n', "\n|    ")
    )
}

/// Print a warning with a given context applied. The warning becomes indented
/// beneath the context.
#[inline]
pub(crate) fn print_warning_with_context<E: Display, C: Display>(
    warning: E,
    context: impl FnOnce() -> C,
) {
    eprintln!("{}", warning_with_context(warning, context));
}

/// A struct wrapping any type which also holds any number of warnings.
#[derive(Debug)]
pub struct Logger<T, W = BasicWarning> {
    value: T,
    warnings: W,
}

pub type BasicLogger<T> = Logger<T, BasicWarning>;
pub type AtomicLogger<T> = Logger<T, AtomicWarning>;

impl<T, E, W: Warning> Logger<Result<T, E>, W> {
    /// Converts a [`Logger`] of a [`Result`] to a [`Result`] of a [`Logger`].
    #[inline]
    pub fn transpose(self) -> Result<Logger<T, W>, E> {
        Ok(Logger {
            value: self.value?,
            warnings: self.warnings,
        })
    }
}

impl<T, W> Logger<T, W> {
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
}

impl<T, W: Warning> Logger<T, W> {
    /// Wraps an existing value in a [`Logger`] with no warnings.
    #[inline]
    pub fn new(value: T) -> Self {
        Self {
            value,
            warnings: W::new(),
        }
    }

    /// Returns whether any warnings are being stored by the [`Logger`].
    #[inline]
    pub fn has_warning(&self) -> bool {
        !self.warnings.borrow_vec().is_empty()
    }

    /// Adds a warning to the [`Logger`].
    #[inline]
    pub fn log(&self, warning: impl Display) {
        self.warnings.borrow_mut_vec().push(warning.to_string());
    }

    /// Adds a warning to the [`Logger`] with a context applied. The warning
    /// appears indented beneath the context.
    #[inline]
    pub fn log_with_context<C: Display>(&self, warning: impl Display, context: impl FnOnce() -> C) {
        self.log(warning_with_context(warning, context));
    }

    /// Transforms the value stored in the [`Logger`].
    #[inline]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Logger<U, W> {
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
            self.warnings = W::new_with(vec![warning]);
        }
        self
    }

    /// Converts the logger to an error while applying a context. The warnings
    /// appear indented beneath the context.
    pub fn as_err_with_context<C: Display>(&self, context: impl FnOnce() -> C) -> Option<Error> {
        Some(anyhow!(self.with_context_helper(context)?))
    }

    /// Unwraps the value of a [`Logger`], taking its warnings and logging them
    /// in a new [`Logger`].
    #[inline]
    pub fn relog<S, V: Warning>(self, logger: &Logger<S, V>) -> T {
        for warning in self.warnings.borrow_vec().iter() {
            logger.log(warning);
        }
        self.value
    }

    /// Unwraps the value of a [`Logger`], taking its warnings and sending them.
    #[inline]
    pub fn send(self, tx: impl Borrow<Sender<String>>) -> T {
        for warning in self.warnings.take_vec() {
            tx.borrow().send(warning).unwrap()
        }
        self.value
    }

    /// Unwraps the value of a [`Logger`], taking its warnings and logging them
    /// in a new [`Logger`] with a context applied. The warnings appear indented
    /// beneath the context.
    #[inline]
    pub fn relog_with_context<S, C: Display, V: Warning>(
        self,
        context: impl FnOnce() -> C,
        logger: &Logger<S, V>,
    ) -> T {
        if let Some(warning) = self.with_context_helper(context) {
            logger.log(warning)
        }
        self.value
    }

    /// Unwraps the value of a [`Logger`], taking its warnings and sending them.
    #[inline]
    pub fn send_with_context<C: Display>(
        self,
        context: impl FnOnce() -> C,
        tx: impl Borrow<Sender<String>>,
    ) -> T {
        if let Some(warning) = self.with_context_helper(context) {
            tx.borrow().send(warning).unwrap()
        }
        self.value
    }

    /// Unwraps the value of a [`Logger`], printing its warnings.
    #[inline]
    pub fn print_warnings(self) -> T {
        for warning in self.warnings.borrow_vec().iter() {
            eprintln!("{warning}");
        }
        self.value
    }

    /// Unwraps the value of a [`Logger`], printing its warnings with a context
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
                    .borrow_vec()
                    .iter()
                    .map(|x| x.replace('\n', "\n|    "))
                    .intersperse("\n|    ".to_string())
                    .collect::<String>()
        })
    }
}

/// An extension trait for a result containing a [`Logger`] (i.e., a value
/// wrapped with both warnings and a potential error).
pub trait LoggerInResult<T, E, W> {
    /// Applies a context to the [`Logger`], if there is no error. The warnings
    /// appear indented beneath the context.
    #[must_use]
    fn warnings_with_context<C: Display>(self, context: impl FnOnce() -> C) -> Self;

    /// Transforms the value stored in the [`Logger`] within the [`Result`].
    fn map_val<U>(self, f: impl FnOnce(T) -> U) -> Result<Logger<U, W>, E>;
}

impl<T, E, W: Warning> LoggerInResult<T, E, W> for Result<Logger<T, W>, E> {
    #[inline]
    fn warnings_with_context<C: Display>(mut self, context: impl FnOnce() -> C) -> Self {
        if let Ok(log) = &mut self
            && let Some(warning) = log.with_context_helper(context)
        {
            log.warnings = W::new_with(vec![warning]);
        }
        self
    }

    #[inline]
    fn map_val<U>(self, f: impl FnOnce(T) -> U) -> Result<Logger<U, W>, E> {
        self.map(|log| Logger {
            value: f(log.value),
            warnings: log.warnings,
        })
    }
}

/// An extension trait for iterators whose items are results. It provides the
/// ability to filter errors from the iterator and record them as warnings.
pub trait LogErrors: Iterator {
    /// Filters the errors from an iterator of results, logging them as warnings
    /// to `logger`.
    #[inline]
    fn log_errors<S, T, W: Warning, E: Display>(
        self,
        logger: &Logger<S, W>,
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
    fn log_errors_with_message<S, T, W: Warning, E>(
        self,
        logger: &Logger<S, W>,
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
    /// to `logger` with a context applied. The warnings appear indented beneath
    /// the context.
    #[inline]
    fn log_errors_with_context<'a, S, T, W: Warning, E: Display, C: Display>(
        self,
        logger: &'a Logger<S, W>,
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

pub trait SendErrors: ParallelIterator {
    /// Filters the errors from an iterator of results, logging them as warnings
    /// to `logger`.
    #[inline]
    fn send_errors<T, E>(
        self,
        tx: impl Borrow<Sender<String>> + Sync + Send,
    ) -> rayon::iter::FilterMap<Self, impl Fn(Result<T, E>) -> Option<T> + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Result<T, E>>,
        T: Sync + Send,
        E: Display,
    {
        self.filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(e) => {
                tx.borrow().send(e.to_string()).unwrap();
                None
            }
        })
    }

    #[inline]
    fn send_errors_with_message<T, E>(
        self,
        tx: Sender<String>,
        message: String,
    ) -> rayon::iter::FilterMap<Self, impl Fn(Result<T, E>) -> Option<T> + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Result<T, E>>,
        T: Sync + Send,
    {
        self.filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(_) => {
                tx.send(message.clone()).unwrap();
                None
            }
        })
    }

    #[inline]
    fn send_errors_with_context<T, E, C, P>(
        self,
        tx: Sender<String>,
        context: P,
    ) -> rayon::iter::FilterMap<Self, impl Fn(Result<T, E>) -> Option<T> + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Result<T, E>>,
        E: Display,
        C: Display + Send,
        P: Fn() -> C + Sync + Send,
        T: Sync + Send,
    {
        self.filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(e) => {
                tx.send(warning_with_context(e, &context)).unwrap();
                None
            }
        })
    }
}

impl<I, T, E> SendErrors for I where I: ParallelIterator<Item = Result<T, E>> {}

/// An extension trait for iterators whose items are loggers. It provides the
/// ability to unwrap the values in the iterator and relog the warnings.
pub trait LogWarnings: Iterator {
    /// Relogs all warnings in an iterator, unwrapping each [`Logger`].
    #[inline]
    fn log_warnings<S, T, W: Warning, V: Warning>(
        self,
        logger: &Logger<S, W>,
    ) -> Map<Self, impl FnMut(Logger<T, V>) -> T>
    where
        Self: Sized + Iterator<Item = Logger<T, V>>,
    {
        self.into_iter().map(move |item| item.relog(logger))
    }

    /// Relogs all warnings in an iterator with a context applied, unwrapping
    /// each [`Logger`]. The warnings appear indented beneath the context.
    #[inline]
    fn log_warnings_with_context<S, T, W: Warning, V: Warning, C: Display>(
        self,
        logger: &Logger<S, W>,
        context: impl Fn() -> C,
    ) -> Map<Self, impl FnMut(Logger<T, V>) -> T>
    where
        Self: Sized + Iterator<Item = Logger<T, V>>,
    {
        self.into_iter()
            .map(move |item| item.relog_with_context(&context, logger))
    }

    /// Prints all warnings in an iterator, unwrapping each [`Logger`].
    #[inline]
    fn print_warnings<T, W: Warning>(self) -> Map<Self, impl FnMut(Logger<T, W>) -> T>
    where
        Self: Sized + Iterator<Item = Logger<T, W>>,
    {
        self.into_iter().map(move |item| item.print_warnings())
    }
}

impl<I, T, W> LogWarnings for I where I: Iterator<Item = Logger<T, W>> {}

pub trait SendWarnings: ParallelIterator {
    /// Relogs all warnings in an iterator, unwrapping each [`Logger`].
    #[inline]
    fn send_warnings<T, W>(
        self,
        tx: impl Borrow<Sender<String>> + Sync + Send,
    ) -> rayon::iter::Map<Self, impl Fn(Logger<T, W>) -> T + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Logger<T, W>>,
        T: Send,
        W: Warning,
    {
        self.map(move |item| item.send(tx.borrow()))
    }

    /// Relogs all warnings in an iterator with a context applied, unwrapping
    /// each [`Logger`]. The warnings appear indented beneath the context.
    #[inline]
    fn send_warnings_with_context<T: Send, W: Warning, C: Display>(
        self,
        tx: Sender<String>,
        context: impl Fn() -> C + Send + Sync,
    ) -> rayon::iter::Map<Self, impl Fn(Logger<T, W>) -> T + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Logger<T, W>>,
    {
        self.map(move |item| item.send_with_context(&context, &tx))
    }
}

impl<I, T, W> SendWarnings for I where I: ParallelIterator<Item = Logger<T, W>> {}

/// A fallible version of [`FromIterator`], where any item that fails generates
/// a warning in the [`Logger`].
pub trait FromIteratorWithWarnings<A, W>: Sized {
    /// Builds a collection from an iterator, where processing of each item may
    /// fail. Any failed items generate a warning in the [`Logger`].
    #[must_use]
    fn from_iter_with_warnings<T: IntoIterator<Item = A>>(iter: T) -> Logger<Self, W>;
}

/// A fallible version of [`collect`]. See [`FromIteratorWithWarnings`] for more
/// details.
///
/// [`collect`]: std::iter::Iterator::collect
pub trait CollectWithWarnings<T>: Iterator<Item = T> {
    /// Builds a collection from an iterator, where processing of each item may
    /// fail. Any failed items generate a warning in the [`Logger`].
    #[inline]
    #[must_use]
    fn collect_with_warnings<B>(self) -> Logger<B, BasicWarning>
    where
        Self: Sized,
        B: FromIteratorWithWarnings<T, BasicWarning>,
    {
        FromIteratorWithWarnings::from_iter_with_warnings(self)
    }

    #[inline]
    #[must_use]
    fn collect_with_warnings_atomic<B>(self) -> Logger<B, AtomicWarning>
    where
        Self: Sized,
        B: FromIteratorWithWarnings<T, AtomicWarning>,
    {
        FromIteratorWithWarnings::from_iter_with_warnings(self)
    }
}

impl<T, I: Iterator<Item = T>> CollectWithWarnings<T> for I {}

// pub struct Logger<T>(LoggerBase<T, BasicWarning>);
// pub struct AtomicLogger<T>(LoggerBase<T, AtomicWarning>);

// pub trait AnyLogger<T> {
//     pub fn transpose(self) -> Result<LoggerBase<T, W>, E>
// }

// impl<T> From<LoggerBase<T, BasicWarning>> for Logger<T> {
//     #[inline]
//     fn from(value: LoggerBase<T, BasicWarning>) -> Self {
//         Logger(value)
//     }
// }

// impl<T> From<LoggerBase<T, AtomicWarning>> for AtomicLogger<T> {
//     #[inline]
//     fn from(value: LoggerBase<T, AtomicWarning>) -> Self {
//         AtomicLogger(value)
//     }
// }
