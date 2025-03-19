use std::{
    cell::{Ref, RefCell, RefMut},
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::{Arc, Mutex, MutexGuard},
};

pub trait Warning {
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

pub(crate) type BasicWarning = Rc<RefCell<Vec<String>>>;

impl Warning for BasicWarning {
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
        RefCell::borrow(self)
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

pub(crate) type AtomicWarning = Arc<Mutex<Vec<String>>>;

impl Warning for AtomicWarning {
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
