use alloc;
use alloc::heap;
use std::borrow::Borrow;
use std::cmp;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::mem;
use std::ptr;
use std::slice;

// statistically, 99.86% of our label tokens and 100% of our math tokens are at most 15
// characters.  actually, math tokens are usually under 8 characters when sampled by
// dynamic frequency, but let's try a single representation for now.

#[unsafe_no_drop_flag]
#[derive(Default)]
pub struct IToken {
    _content: [usize; 2],
}

fn word_size() -> usize {
    mem::size_of::<usize>()
}

fn round_up(val: usize) -> usize {
    (val + word_size() - 1) & word_size().wrapping_neg()
}

#[cold]
#[inline(never)]
fn from_slice_slow(sl: &[u8]) -> IToken {
    let words = 1 + round_up(sl.len()) / word_size();
    unsafe {
        let vptr = heap::allocate(words * word_size(), word_size()) as *mut usize;
        if vptr.is_null() {
            alloc::oom();
        }
        *vptr.offset(words as isize - 1) = 0;
        *vptr.offset(0) = sl.len();
        ptr::copy_nonoverlapping(sl.as_ptr(), vptr.offset(1) as usize as *mut _, sl.len());
        IToken { _content: [vptr as usize, !0] }
    }
}

impl IToken {
    fn max_inline() -> usize {
        cmp::min(2 * word_size() - 1, 0xFE)
    }

    fn inline_ref(&self) -> *const u8 {
        unsafe { mem::transmute(self) }
    }

    fn tag_ref(&self) -> *const u8 {
        unsafe { self.inline_ref().offset(2 * word_size() as isize - 1) }
    }

    fn is_outofline(&self) -> bool {
        unsafe { *self.tag_ref() == !0 }
    }

    pub fn from_slice(sl: &[u8]) -> IToken {
        if sl.len() <= IToken::max_inline() {
            unsafe {
                let res = IToken::default();
                ptr::copy_nonoverlapping(sl.as_ptr(), res.inline_ref() as *mut _, sl.len());
                *(res.tag_ref() as *mut u8) = sl.len() as u8;
                res
            }
        } else {
            from_slice_slow(sl)
        }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe {
            let tag = *self.tag_ref();
            if tag == 0xFF {
                let buffer = self._content[0] as *const usize;
                let len = *buffer;
                let start = buffer.offset(1) as usize as *const u8;
                slice::from_raw_parts(start, len)
            } else {
                let len = tag as usize;
                let start = self as *const _ as usize as *const u8;
                slice::from_raw_parts(start, len)
            }
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn drop_slow(ptr: usize) {
    if mem::POST_DROP_USIZE != !0 || ptr != mem::POST_DROP_USIZE {
        let vptr = ptr as *mut usize;
        let len = *vptr;
        let words = 1 + round_up(len) / word_size();
        heap::deallocate(vptr as *mut u8, words * word_size(), word_size());
    }
}

impl Drop for IToken {
    fn drop(&mut self) {
        if self.is_outofline() {
            unsafe { drop_slow(self._content[0]); }
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn clone_slow(tok: &IToken) -> IToken {
    let vptr = tok._content[0] as *const usize;
    let len = *vptr;
    let words = 1 + round_up(len) / word_size();
    let newptr = heap::allocate(words * word_size(), word_size()) as *mut usize;
    if newptr.is_null() {
        alloc::oom();
    }
    ptr::copy_nonoverlapping(vptr, newptr, words);
    IToken { _content: [newptr as usize, !0] }
}

impl Clone for IToken {
    fn clone(&self) -> IToken {
        if self.is_outofline() {
            unsafe {
                clone_slow(self)
            }
        } else {
            IToken { _content: self._content }
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn eq_slow(tok: &IToken, other: &IToken) -> bool {
    if !other.is_outofline() {
        return false;
    }

    let sptr = tok._content[0] as *const usize;
    let optr = other._content[0] as *const usize;
    let slen = *sptr;
    let olen = *optr;
    if slen != olen {
        return false;
    }

    let wordsm1 = round_up(slen) / word_size();
    slice::from_raw_parts(sptr.offset(1), wordsm1) == slice::from_raw_parts(optr.offset(1), wordsm1)
}

impl PartialEq for IToken {
    fn eq(&self, other: &IToken) -> bool {
        if self.is_outofline() {
            unsafe { eq_slow(self, other) }
        } else {
            self._content[0] == other._content[0] && self._content[1] == other._content[1]
        }
    }
}

impl Eq for IToken {}

impl Hash for IToken {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl fmt::Debug for IToken {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        String::from_utf8_lossy(self.as_slice()).fmt(f)
    }
}

/// Thin wrapper around a native slice which guarantees to do hashing in an
/// IToken-compatible way.
#[derive(PartialEq,Eq)]
pub struct ITokenRef([u8]);

impl ITokenRef {
    pub fn from(sl: &[u8]) -> &ITokenRef {
        unsafe { mem::transmute(sl) }
    }

    pub fn as_slice(&self) -> &[u8] {
        unsafe { mem::transmute(self) }
    }
}

impl Hash for ITokenRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl fmt::Debug for ITokenRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        String::from_utf8_lossy(self.as_slice()).fmt(f)
    }
}

impl Borrow<ITokenRef> for IToken {
    fn borrow(&self) -> &ITokenRef {
        ITokenRef::from(self.as_slice())
    }
}

impl ToOwned for ITokenRef {
    type Owned = IToken;
    fn to_owned(&self) -> IToken {
        IToken::from_slice(self.as_slice())
    }
}