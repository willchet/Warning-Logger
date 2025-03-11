#![feature(iter_intersperse, let_chains)]

use anyhow::{Result, anyhow};
use rayon::iter::ParallelIterator;
use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::Display,
    iter::{FilterMap, Map},
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::{Arc, Mutex, MutexGuard, mpsc::Sender},
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

mod sealed {
    pub trait Sealed {}
}
use sealed::Sealed;

pub trait Warnings: Sealed {
    type BorrowedVec<'a>: Deref<Target = Vec<String>>
    where
        Self: 'a;
    type BorrowedMutVec<'a>: DerefMut<Target = Vec<String>>
    where
        Self: 'a;

    fn new() -> Self;
    fn new_with(warnings: Vec<String>) -> Self;
    fn borrow_vec(&self) -> Self::BorrowedVec<'_>;
    fn borrow_mut_vec(&self) -> Self::BorrowedMutVec<'_>;
    fn take_vec(self) -> Vec<String>;
}

impl Sealed for Rc<RefCell<Vec<String>>> {}

impl Warnings for Rc<RefCell<Vec<String>>> {
    type BorrowedVec<'a> = Ref<'a, Vec<String>>;
    type BorrowedMutVec<'a> = RefMut<'a, Vec<String>>;

    #[inline]
    fn new() -> Self {
        Rc::new(RefCell::new(vec![]))
    }

    #[inline]
    fn new_with(warnings: Vec<String>) -> Self {
        Rc::new(RefCell::new(warnings))
    }

    #[inline]
    fn borrow_vec(&self) -> Ref<'_, Vec<String>> {
        self.borrow()
    }

    #[inline]
    fn borrow_mut_vec(&self) -> RefMut<'_, Vec<String>> {
        self.borrow_mut()
    }

    #[inline]
    fn take_vec(self) -> Vec<String> {
        self.take()
    }
}

impl Sealed for Arc<Mutex<Vec<String>>> {}

impl Warnings for Arc<Mutex<Vec<String>>> {
    type BorrowedVec<'a> = MutexGuard<'a, Vec<String>>;
    type BorrowedMutVec<'a> = MutexGuard<'a, Vec<String>>;

    #[inline]
    fn new() -> Self {
        Arc::new(Mutex::new(vec![]))
    }

    #[inline]
    fn new_with(warnings: Vec<String>) -> Self {
        Arc::new(Mutex::new(warnings))
    }

    #[inline]
    fn borrow_vec(&self) -> MutexGuard<'_, Vec<String>> {
        self.lock().unwrap()
    }

    #[inline]
    fn borrow_mut_vec(&self) -> MutexGuard<'_, Vec<String>> {
        self.lock().unwrap()
    }

    #[inline]
    fn take_vec(self) -> Vec<String> {
        Arc::into_inner(self).unwrap().into_inner().unwrap()
    }
}

/// A struct wrapping any type which also holds any number of warnings.
#[derive(Debug)]
pub struct Logger<T, W = Rc<RefCell<Vec<String>>>> {
    value: T,
    warnings: W,
}

pub type AtomicLogger<T> = Logger<T, Arc<Mutex<Vec<String>>>>;

impl<T, E, W: Warnings> Logger<Result<T, E>, W> {
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

impl<T, W: Warnings> Logger<T, W> {
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

    /// Unwraps the value of a [`Logger`], taking its warnings and logging them
    /// in a new [`Logger`].
    #[inline]
    pub fn relog<S, V: Warnings>(self, logger: &Logger<S, V>) -> T {
        for warning in self.warnings.borrow_vec().iter() {
            logger.log(warning);
        }
        self.value
    }

    /// Unwraps the value of a [`Logger`], taking its warnings and sending them.
    #[inline]
    pub fn send(self, tx: &Sender<String>) -> T {
        for warning in self.warnings.take_vec() {
            tx.send(warning).unwrap()
        }
        self.value
    }

    /// Unwraps the value of a [`Logger`], taking its warnings and logging them
    /// in a new [`Logger`] with a context applied. The warnings appear indented
    /// beneath the context.
    #[inline]
    pub fn relog_with_context<S, C: Display, V: Warnings>(
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
        tx: &Sender<String>,
    ) -> T {
        if let Some(warning) = self.with_context_helper(context) {
            tx.send(warning).unwrap()
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

impl<T, E, W: Warnings> LoggerInResult<T, E, W> for Result<Logger<T, W>, E> {
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

/// An extension trait allowing any value to be wrapped into a [`Logger`].
pub trait LoggingWrap<W: Warnings>: Sized {
    /// Wraps the value in a [`Logger`] with no warnings.
    #[inline]
    #[must_use]
    fn wrap(self) -> Logger<Self, W> {
        Logger::<Self, W>::new(self)
    }

    /// Wraps the value in a [`Logger`] with a set of warnings.
    #[inline]
    #[must_use]
    fn wrap_with_warnings(self, warnings: Logger<(), W>) -> Logger<Self, W> {
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
        warnings: Logger<(), W>,
    ) -> Logger<Self, W> {
        let warnings = warnings.with_context(context).warnings;
        Logger {
            value: self,
            warnings,
        }
    }
}

impl<T, W: Warnings> LoggingWrap<W> for T {}

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
    /// to `logger`.
    #[inline]
    fn log_errors<S, T, W: Warnings, E: Display>(
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
    fn log_errors_with_message<S, T, W: Warnings, E>(
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
    fn log_errors_with_context<'a, S, T, W: Warnings, E: Display, C: Display>(
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
        tx: &Sender<String>,
    ) -> rayon::iter::FilterMap<Self, impl Fn(Result<T, E>) -> Option<T> + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Result<T, E>>,
        T: Sync + Send,
        E: Display,
    {
        self.filter_map(move |item| match item {
            Ok(value) => Some(value),
            Err(e) => {
                tx.send(e.to_string()).unwrap();
                None
            }
        })
    }

    #[inline]
    fn send_errors_with_message<T, E>(
        self,
        tx: &Sender<String>,
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
        tx: &Sender<String>,
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
    fn log_warnings<S, T, W: Warnings, V: Warnings>(
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
    fn log_warnings_with_context<S, T, W: Warnings, V: Warnings, C: Display>(
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
    fn print_warnings<T, W: Warnings>(self) -> Map<Self, impl FnMut(Logger<T, W>) -> T>
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
        tx: &Sender<String>,
    ) -> rayon::iter::Map<Self, impl Fn(Logger<T, W>) -> T + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Logger<T, W>>,
        T: Send,
        W: Warnings,
    {
        self.map(move |item| item.send(tx))
    }

    /// Relogs all warnings in an iterator with a context applied, unwrapping
    /// each [`Logger`]. The warnings appear indented beneath the context.
    #[inline]
    fn send_warnings_with_context<T: Send, W: Warnings, C: Display>(
        self,
        tx: &Sender<String>,
        context: impl Fn() -> C + Send + Sync,
    ) -> rayon::iter::Map<Self, impl Fn(Logger<T, W>) -> T + Sync + Send>
    where
        Self: Sized + ParallelIterator<Item = Logger<T, W>>,
    {
        self.map(move |item| item.send_with_context(&context, tx))
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
pub trait CollectWithWarning<T>: Iterator<Item = T> {
    /// Builds a collection from an iterator, where processing of each item may
    /// fail. Any failed items generate a warning in the [`Logger`].
    #[inline]
    #[must_use]
    fn collect_with_warnings<B, W>(self) -> Logger<B, W>
    where
        Self: Sized,
        B: FromIteratorWithWarnings<T, W>,
    {
        FromIteratorWithWarnings::from_iter_with_warnings(self)
    }
}

impl<T, I: Iterator<Item = T>> CollectWithWarning<T> for I {}

// pub struct Logger<T>(LoggerBase<T, Rc<RefCell<Vec<String>>>>);
// pub struct AtomicLogger<T>(LoggerBase<T, Arc<Mutex<Vec<String>>>>);

// pub trait AnyLogger<T> {
//     pub fn transpose(self) -> Result<LoggerBase<T, W>, E>
// }

// impl<T> From<LoggerBase<T, Rc<RefCell<Vec<String>>>>> for Logger<T> {
//     #[inline]
//     fn from(value: LoggerBase<T, Rc<RefCell<Vec<String>>>>) -> Self {
//         Logger(value)
//     }
// }

// impl<T> From<LoggerBase<T, Arc<Mutex<Vec<String>>>>> for AtomicLogger<T> {
//     #[inline]
//     fn from(value: LoggerBase<T, Arc<Mutex<Vec<String>>>>) -> Self {
//         AtomicLogger(value)
//     }
// }
