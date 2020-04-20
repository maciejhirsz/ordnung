use alloc::vec::{Vec as StdVec, IntoIter};
use core::fmt;
use core::iter::FromIterator;
use core::mem::ManuallyDrop;
use core::ptr::{NonNull, slice_from_raw_parts_mut, slice_from_raw_parts};

pub struct Vec<T> {
    ptr: NonNull<[T]>,
}

impl<T> Vec<T> {
    pub fn new() -> Self {
        Self::from_stdvec_unchecked(StdVec::new())
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self::from_stdvec_unchecked(StdVec::with_capacity(capacity))
    }

    pub fn push(&mut self, val: T) {
        let ptr = self.as_mut_ptr();
        let (len, cap) = self.parts();

        if len == cap {
            let new_cap = match cap {
                0 => 1,
                n => n * 2,
            };
            // Create a new bigger buffer
            let mut svec = ManuallyDrop::new(StdVec::with_capacity(new_cap));

            unsafe {
                // Copy contents
                core::ptr::copy_nonoverlapping(ptr, svec.as_mut_ptr(), len);

                // Drop old buffer, len 0 (we don't want to drop content)
                core::mem::drop(StdVec::from_raw_parts(ptr, 0, cap));
            }

            self.ptr = unsafe { pack_unchecked(svec.as_mut_ptr(), len, svec.capacity()) }
        }
        unsafe { self.as_mut_ptr().add(len).write(val) }
        self.set_len(len + 1);
    }

    pub fn pop(&mut self) -> Option<T> {
        let len = self.len().checked_sub(1)?;

        self.set_len(len);

        Some(unsafe {
            self.as_mut_ptr().add(len).read()
        })
    }

    pub fn clear(&mut self) {
        self.with(move |v| v.clear())
    }

    pub fn len(&self) -> usize {
        let (len, _) = self.parts();

        len
    }

    pub fn capacity(&self) -> usize {
        let (_, cap) = self.parts();

        cap
    }

    pub fn remove(&mut self, index: usize) -> T {
        self.with(move |v| v.remove(index))
    }

    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.ptr.cast().as_ptr()
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr.cast().as_ptr()
    }

    fn set_len(&mut self, len: usize) {
        let (_, cap) = self.parts();

        self.ptr = unsafe {
            pack_unchecked(
                self.as_mut_ptr(),
                len,
                cap,
            )
        };
    }

    #[inline]
    fn parts(&self) -> (usize, usize) {
        let parts = unsafe { &*self.ptr.as_ptr() }.len();

        (parts & MASK_LO, (parts & MASK_HI) >> 32)
    }

    fn with<'a, R: 'a, F: FnOnce(&mut StdVec<T>) -> R>(&mut self, f: F) -> R {
        let (len, cap) = self.parts();

        let mut svec = unsafe {
            StdVec::from_raw_parts(self.as_mut_ptr(), len, cap)
        };

        let r = f(&mut svec);

        ManuallyDrop::new(core::mem::replace(self, Self::from_stdvec_unchecked(svec)));

        r
    }

    fn into_inner(self) -> StdVec<T> {
        let mut vec = ManuallyDrop::new(self);
        let ptr = vec.as_mut_ptr();
        let (len, cap) = vec.parts();

        unsafe {
            StdVec::from_raw_parts(ptr, len, cap)
        }
    }

    fn from_stdvec_unchecked(svec: StdVec<T>) -> Self {
        let mut svec = ManuallyDrop::new(svec);

        let (ptr, len, cap) = (svec.as_mut_ptr(), svec.len(), svec.capacity());

        let ptr = slice_from_raw_parts_mut(
            ptr,
            len & MASK_LO | (cap & MASK_LO) << 32,
        );

        Vec {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }

    fn inner_ref<'a>(&'a self) -> &'a [T] {
        let (len, _) = self.parts();

        unsafe {
            &*slice_from_raw_parts(self.as_ptr() as *mut T, len)
        }
    }

    fn inner_mut<'a>(&'a mut self) -> &'a mut [T] {
        let (len, _) = self.parts();

        unsafe {
            &mut*slice_from_raw_parts_mut(self.as_mut_ptr() as *mut T, len)
        }
    }
}

impl<T> core::ops::Drop for Vec<T> {
    fn drop(&mut self) {
        let (len, cap) = self.parts();

        unsafe {
            StdVec::from_raw_parts(self.as_mut_ptr(), len, cap);
        }
    }
}

impl<T> From<StdVec<T>> for Vec<T> {
    fn from(stdvec: StdVec<T>) -> Self {
        let mut stdvec = ManuallyDrop::new(stdvec);

        let ptr = stdvec.as_mut_ptr();
        let len = stdvec.len();
        let cap = stdvec.capacity();

        Vec {
            ptr: unsafe { pack(ptr, len, cap) },
        }
    }
}

impl<T: Clone> Clone for Vec<T> {
    fn clone(&self) -> Vec<T> {
        Vec::from_stdvec_unchecked((&**self).to_vec())
    }
}

impl<T> core::ops::Deref for Vec<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.inner_ref()
    }
}

impl<T> core::ops::DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.inner_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for Vec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_ref().fmt(f)
    }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        self.into_inner().into_iter()
    }
}

impl<T> FromIterator<T> for Vec<T> {
    fn from_iter<I>(iter: I) -> Vec<T>
    where
        I: IntoIterator<Item = T>,
    {
        Self::from_stdvec_unchecked(StdVec::from_iter(iter))
    }
}

impl<T: PartialEq> PartialEq for Vec<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        self.inner_ref() == other.inner_ref()
    }
}

unsafe impl<T: Sync> Sync for Vec<T> {}
unsafe impl<T: Send> Send for Vec<T> {}


const MASK_LO: usize = core::u32::MAX as usize;
const MASK_HI: usize = !(core::u32::MAX as usize);


#[inline]
unsafe fn pack<T>(ptr: *mut T, len: usize, capacity: usize) -> NonNull<[T]> {
    if (capacity & MASK_HI) != 0 {
        panic!("compact Vec capacity out of bounds");
    }

    pack_unchecked(ptr, len, capacity)
}


#[inline]
unsafe fn pack_unchecked<T>(ptr: *mut T, len: usize, capacity: usize) -> NonNull<[T]> {
    NonNull::new_unchecked(
        slice_from_raw_parts_mut(
            ptr as *mut T,
            (len & MASK_LO) | ((capacity & MASK_LO) << 32)
        )
    )
}
