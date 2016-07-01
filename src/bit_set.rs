//! Mini-library for an optimized `HashSet<usize>` which reduces to bit
//! operations for a small universe.
//!
//! The current implementation falls back to bit operations on a large dense
//! array, which would be problematic if sparse; however, this is used to
//! support the verifier, and will never see an index larger than ~40 on the
//! standard set.mm.  (Thus, on a 64-bit build the fallback code doesn't get
//! exercised at all without special measures.)

use std::ops::BitOrAssign;
use std::cmp::PartialOrd;
use std::cmp::Ordering;
use std::slice;


/// A set of variable indices.
#[derive(Default,Debug,PartialEq,Eq)]
pub struct Bitset {
    head: usize,
    tail: Option<Box<Vec<usize>>>,
}

fn bits_per_word() -> usize {
    usize::max_value().count_ones() as usize
}

impl Clone for Bitset {
    #[inline]
    fn clone(&self) -> Bitset {
        Bitset {
            head: self.head,
            tail: match self.tail {
                None => None,
                Some(ref tail) => Some(tail.clone()),
            },
        }
    }
}

impl Bitset {
    /// Creates a new empty `Bitset`.  Does not allocate.  Equivalent to
    /// `Bitset::default()`.
    pub fn new() -> Bitset {
        Bitset {
            head: 0,
            tail: None,
        }
    }

    fn tail(&self) -> &[usize] {
        match self.tail {
            None => Default::default(),
            Some(ref bx) => &bx,
        }
    }

    fn tail_mut(&mut self) -> &mut Vec<usize> {
        if self.tail.is_none() {
            self.tail = Some(Box::new(Vec::new()));
        }
        self.tail.as_mut().unwrap()
    }

    /// Adds a single bit to a set.
    pub fn set_bit(&mut self, bit: usize) {
        if bit < bits_per_word() {
            self.head |= 1 << bit;
        } else {
            let word = bit / bits_per_word() - 1;
            let tail = self.tail_mut();
            if word >= tail.len() {
                tail.resize(word + 1, 0);
            }
            tail[word] |= 1 << (bit & (bits_per_word() - 1));
        }
    }

    /// Tests a set for a specific bit.
    pub fn has_bit(&self, bit: usize) -> bool {
        if bit < bits_per_word() {
            (self.head & (1 << bit)) != 0
        } else {
            let word = bit / bits_per_word() - 1;
            let tail = self.tail();
            word < tail.len() && (tail[word] & (1 << (bit & (bits_per_word() - 1)))) != 0
        }
    }

    /// Adds a single bit to a set, and returns the old value.  Equivalent to
    /// `{ let old = bitset.has_bit(bit); bitset.set_bit(bit); old }`.
    pub fn set_bit_if(&mut self, bit: usize) -> bool {
        if bit < bits_per_word() {
            let old = (self.head & (1 << bit)) != 0;
            self.head |= 1 << bit;
            old
        } else {
            let word = bit / bits_per_word() - 1;
            let tail = self.tail_mut();
            let mask = 1 << (bit & (bits_per_word() - 1));
            let old = if word >= tail.len() {
                tail.resize(word + 1, 0);
                false
            } else {
                (tail[word] & mask) != 0
            };
            tail[word] |= mask;
            old
        }
    }

    /// same as `self <= rhs`, but with `rhs` treated as zero if empty
    #[inline]
    pub fn le_opt(&self, rhs: Option<&Bitset>) -> bool {
        match rhs {
            None => *self == Bitset::new(),
            Some(&ref rhs) => *self <= *rhs,
        }
    }
    
}

impl<'a> BitOrAssign<&'a Bitset> for Bitset {
    fn bitor_assign(&mut self, rhs: &'a Bitset) {
        self.head |= rhs.head;
        if let Some(ref rtail) = rhs.tail {
            let stail = self.tail_mut();
            if rtail.len() > stail.len() {
                stail.resize(rtail.len(), 0);
            }
            for i in 0..rtail.len() {
                stail[i] |= rtail[i];
            }
        }
    }
}

impl<'a> PartialOrd<Bitset> for Bitset {
    /// The powerset partial ordering of bit sets: a bit set `L` is less or equal to `R`
    /// if every bit which is set in `L` is also set in `R`. 
    fn le(&self, rhs: &Bitset) -> bool {
        match self.tail {
            None => self.head | rhs.head == rhs.head,
            Some(ref stail) => {
                let rtail = rhs.tail();
                stail.len() <= rtail.len() && (self.head | rhs.head == rhs.head) &&
                (0..stail.len()).all(|i| stail[i] | rtail[i] == rtail[i])
            }
        }
    }
    
    fn ge(&self, rhs: &Bitset) -> bool {
        rhs <= self
    }

    fn lt(&self, rhs: &Bitset) -> bool {
        self <= rhs && self != rhs
    }
    
    fn gt(&self, rhs: &Bitset) -> bool {
        rhs < self
    }

    fn partial_cmp(&self, rhs: &Bitset) -> Option<Ordering> {
        match (self <= rhs, rhs <= self) {
            (true, true) => Some(Ordering::Equal),
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => None,
        }
    }
}

impl<'a> IntoIterator for &'a Bitset {
    type Item = usize;
    type IntoIter = BitsetIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        BitsetIter {
            bits: self.head,
            offset: 0,
            buffer: self.tail().iter(),
        }
    }
}

/// Iterator for set bits in a bitset.
pub struct BitsetIter<'a> {
    bits: usize,
    offset: usize,
    buffer: slice::Iter<'a, usize>,
}

impl<'a> Iterator for BitsetIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.bits == 0 {
            self.offset += bits_per_word();
            match self.buffer.next() {
                Some(bits) => self.bits = *bits,
                None => return None,
            }
        }
        let tz = self.bits.trailing_zeros() as usize;
        self.bits &= self.bits - 1;
        Some(tz + self.offset)
    }
}
