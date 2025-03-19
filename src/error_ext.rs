use std::{borrow::Borrow, fmt::Display, sync::mpsc::Sender};

use anyhow::Error;

use crate::{Logger, Warning, warning_with_context};

pub trait ErrorExt: Sized {
    fn with_context<C: Display>(&self, context: impl FnOnce() -> C) -> String;

    fn log_with_context<T, W: Warning, C: Display>(
        self,
        logger: &Logger<T, W>,
        context: impl FnOnce() -> C,
    );

    fn send_with_context<C: Display>(
        self,
        context: impl FnOnce() -> C,
        tx: impl Borrow<Sender<String>>,
    );
}

impl ErrorExt for Error {
    fn with_context<C: Display>(&self, context: impl FnOnce() -> C) -> String {
        warning_with_context(self, context)
    }

    #[inline]
    fn log_with_context<T, W: Warning, C: Display>(
        self,
        logger: &Logger<T, W>,
        context: impl FnOnce() -> C,
    ) {
        logger.log_with_context(self, context)
    }

    #[inline]
    fn send_with_context<C: Display>(
        self,
        context: impl FnOnce() -> C,
        tx: impl Borrow<Sender<String>>,
    ) {
        tx.borrow()
            .send(warning_with_context(self, context))
            .unwrap()
    }
}
