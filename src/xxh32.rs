use std::mem::{uninitialized,transmute};
use std::ptr::{copy};
use std::hash::{Hash, Hasher};
use std::default::Default;
use std::num::Wrapping;
use std::ops::{Shl, Shr, BitOr};

// unstable
//#[cfg(test)] use test::Bencher;

fn rotl32<T: Shl<usize, Output=T> + Shr<usize, Output=T> + BitOr<T, Output=T> + Clone>(x: T, b: usize) -> T { #![inline(always)]
    ((x.clone() << b) | (x.clone() >> (32 - b)))
}

static PRIME1: Wrapping<u32> = Wrapping(2654435761);
static PRIME2: Wrapping<u32> = Wrapping(2246822519);
static PRIME3: Wrapping<u32> = Wrapping(3266489917);
static PRIME4: Wrapping<u32> = Wrapping(668265263);
static PRIME5: Wrapping<u32> = Wrapping(374761393);

pub fn oneshot(input: &[u8], seed: u32) -> u32 {
    let mut state = XXHasher::new_with_seed(seed);
    state.write(input);
    state.finish() as u32
}

#[derive(Copy)]
pub struct XXHasher {
    // field names match the C implementation
    memory: [u32; 4],
    total_len: u64,
    v1: u32,
    v2: u32,
    v3: u32,
    v4: u32,
    memsize: usize,
    seed: u32,
}

impl XXHasher {
    pub fn new_with_seed(seed: u32) -> XXHasher { #![inline]
        // no need to write it twice
        let mut state: XXHasher = unsafe { uninitialized() };
        state.seed = seed;
        state.reset();
        state
    }

    pub fn new() -> XXHasher { #![inline]
        XXHasher::new_with_seed(0)
    }

    fn reset(&mut self) { #![inline]
        self.v1 = (Wrapping(self.seed) + PRIME1 + PRIME2).0;
        self.v2 = (Wrapping(self.seed) + PRIME2).0;
        self.v3 = self.seed;
        self.v4 = (Wrapping(self.seed) - PRIME1).0;
        self.total_len = 0;
        self.memsize = 0;
    }
}

impl Hasher for XXHasher {


    /// Can be called on intermediate states
    fn finish(&self) -> u64 { unsafe {
        let mut rem = self.memsize;
        let mut h32: Wrapping<u32> = if self.total_len < 16 {
            Wrapping(self.seed) + PRIME5
        } else {
            rotl32(Wrapping(self.v1), 1) + rotl32(Wrapping(self.v2), 7) + rotl32(Wrapping(self.v3), 12) + rotl32(Wrapping(self.v4), 18)
        };

        let mut p: *const u8 = transmute(&self.memory);
        macro_rules! read(($size:ty) => (Wrapping(read_ptr!(p, rem, $size) as u32)));

        h32 = h32 + Wrapping(self.total_len as u32);

        while rem >= 4 {
            h32 = h32 + read!(u32) * PRIME3;
            h32 = rotl32(h32, 17) * PRIME4;
        }

        while rem > 0 {
            h32 = h32 + read!(u8) * PRIME5;
            h32 = rotl32(h32, 11) * PRIME1;
        }

        h32 = h32.clone() ^ (h32.clone() >> 15);
        h32 = h32 * PRIME2;
        h32 = h32.clone() ^ (h32.clone() >> 13);
        h32 = h32 * PRIME3;
        h32 = h32.clone() ^ (h32.clone() >> 16);

        h32.0 as u64
    }}

    fn write(&mut self, input: &[u8]) { unsafe {
        let mem: *mut u8 = transmute(&self.memory);
        let mut rem: usize = input.len();
        let mut data: *const u8 = input.as_ptr();

        self.total_len += rem as u64;

        if self.memsize + rem < 16 {
            // not enough data for one 32-byte chunk, so just fill the buffer and return.
            let dst: *mut u8 = mem.offset(self.memsize as isize);
            copy(data, dst, rem);
            self.memsize += rem;
            return;
        }

        if self.memsize != 0 {
            // some data left from previous update
            // fill the buffer and eat it
            let dst: *mut u8 = mem.offset(self.memsize as isize);
            let bump: usize = 16 - self.memsize;
            copy(data, dst, bump);
            let mut p: *const u8 = transmute(mem);
            let mut r: usize = 32;

            macro_rules! read(() => (Wrapping(read_ptr!(p, r, u32))));

            macro_rules! eat(($v: ident) => ({
                $v = $v + read!() * PRIME2; $v = rotl32($v, 13); $v = $v * PRIME1;
            }));

            let mut v1: Wrapping<u32> = Wrapping(self.v1);
            let mut v2: Wrapping<u32> = Wrapping(self.v2);
            let mut v3: Wrapping<u32> = Wrapping(self.v3);
            let mut v4: Wrapping<u32> = Wrapping(self.v4);

            eat!(v1); eat!(v2); eat!(v3); eat!(v4);

            self.v1 = v1.0;
            self.v2 = v2.0;
            self.v3 = v3.0;
            self.v4 = v4.0;

            data = data.offset(bump as isize);
            rem -= bump;
            self.memsize = 0;
        }

        {
            macro_rules! read(() => (Wrapping(read_ptr!(data, rem, u32))));

            macro_rules! eat(($v: ident) => ({
                $v = $v + read!() * PRIME2; $v = rotl32($v, 13); $v = $v * PRIME1;
            }));

            let mut v1: Wrapping<u32> = Wrapping(self.v1);
            let mut v2: Wrapping<u32> = Wrapping(self.v2);
            let mut v3: Wrapping<u32> = Wrapping(self.v3);
            let mut v4: Wrapping<u32> = Wrapping(self.v4);

            while rem >= 16 {
                eat!(v1); eat!(v2); eat!(v3); eat!(v4);
            }

            self.v1 = v1.0;
            self.v2 = v2.0;
            self.v3 = v3.0;
            self.v4 = v4.0;
        }

        if rem > 0 {
            copy(data, mem, rem);
            self.memsize = rem;
        }
    }}

}

impl Clone for XXHasher {
    fn clone(&self) -> XXHasher { #![inline]
        *self
    }
}

impl Default for XXHasher {
    fn default() -> XXHasher { #![inline]
        XXHasher::new()
    }
}

pub fn hash<T: Hash>(value: &T) -> u64 { #![inline]
    let mut state = XXHasher::new_with_seed(0);
    value.hash(&mut state);
    state.finish() as u64
}

pub fn hash_with_seed<T: Hash>(seed: u64, value: &T) -> u64 { #![inline]
    let mut state = XXHasher::new_with_seed(seed as u32);
    value.hash(&mut state);
    state.finish() as u64
}

/// the official sanity test
#[cfg(test)]
fn test_base<F>(f: F)
    where F: Fn(&[u8], u32) -> u32
{ #![inline(always)]
    static BUFSIZE: usize = 101;
    static PRIME: u32 = 2654435761;

    let mut random: Wrapping<u32> = Wrapping(PRIME);
    let mut buf: Vec<u8> = Vec::with_capacity(BUFSIZE);
    for _ in 0..BUFSIZE {
        buf.push((random.0 >> 24) as u8);
        random = random * random;
    }

    let test = |size: usize, seed: u32, expected: u32| {
        let result = f(buf.split_at(size).0, seed);
        assert_eq!(result, expected);
    };


    test(1,                0,      0xB85CBEE5);
    test(1,                PRIME,  0xD5845D64);
    test(14,               0,      0xE5AA0AB4);
    test(14,               PRIME,  0x4481951D);
    test(BUFSIZE,          0,      0x1F1AA412);
    test(BUFSIZE,          PRIME,  0x498EC8E2);
}

// unstable
/*#[cfg(test)]
fn bench_base<F>(bench: &mut Bencher, f: F)
    where F: Fn(&[u8]) -> u32
{ #![inline(always)]
    static BUFSIZE: usize = 64*1024;

    let mut v: Vec<u8> = Vec::with_capacity(BUFSIZE);
    for i in 0..BUFSIZE {
        v.push(i as u8);
    }

    bench.iter( || f(v.as_slice()) );
    bench.bytes = BUFSIZE as u64;
}*/

#[test]
fn test_oneshot() {
    test_base(|v, seed|{
        let mut state = XXHasher::new_with_seed(seed);
        state.write(v);
        state.finish() as u32
    })
}

#[test]
fn test_chunks() {
    test_base(|v, seed|{
        let mut state = XXHasher::new_with_seed(seed);
        for chunk in v.chunks(15) {
            state.write(chunk);
        }
        state.finish() as u32
    })
}

// unstable
/*#[bench]
fn bench_64k_oneshot(b: &mut Bencher) {
    bench_base(b, |v| { oneshot(v, 0) })
}*/

/*
    * The following tests match those of SipHash.
    */


#[test] #[cfg(target_arch = "arm")]
fn test_hash_usize() {
    let val = 0xdeadbeef_deadbeef_u64;
    assert!(hash(&(val as u64)) != hash(&(val as usize)));
    assert_eq!(hash(&(val as u32)), hash(&(val as usize)));
}
#[test] #[cfg(target_arch = "x86_64")]
fn test_hash_usize() {
    let val = 0xdeadbeef_deadbeef_u64;
    assert_eq!(hash(&(val as u64)), hash(&(val as usize)));
    assert!(hash(&(val as u32)) != hash(&(val as usize)));
}
#[test] #[cfg(target_arch = "x86")]
fn test_hash_usize() {
    let val = 0xdeadbeef_deadbeef_u64;
    assert!(hash(&(val as u64)) != hash(&(val as usize)));
    assert_eq!(hash(&(val as u32)), hash(&(val as usize)));
}

#[test]
fn test_hash_idempotent() {
    let val64 = 0xdeadbeef_deadbeef_u64;
    assert_eq!(hash(&val64), hash(&val64));
    let val32 = 0xdeadbeef_u32;
    assert_eq!(hash(&val32), hash(&val32));
}

#[test]
fn test_hash_no_bytes_dropped_64() {
    let val = 0xdeadbeef_deadbeef_u64;

    assert!(hash(&val) != hash(&zero_byte(val, 0)));
    assert!(hash(&val) != hash(&zero_byte(val, 1)));
    assert!(hash(&val) != hash(&zero_byte(val, 2)));
    assert!(hash(&val) != hash(&zero_byte(val, 3)));
    assert!(hash(&val) != hash(&zero_byte(val, 4)));
    assert!(hash(&val) != hash(&zero_byte(val, 5)));
    assert!(hash(&val) != hash(&zero_byte(val, 6)));
    assert!(hash(&val) != hash(&zero_byte(val, 7)));

    fn zero_byte(val: u64, byte: usize) -> u64 {
        assert!(byte < 8);
        val & !(0xff << (byte * 8))
    }
}

#[test]
fn test_hash_no_bytes_dropped_32() {
    let val = 0xdeadbeef_u32;

    assert!(hash(&val) != hash(&zero_byte(val, 0)));
    assert!(hash(&val) != hash(&zero_byte(val, 1)));
    assert!(hash(&val) != hash(&zero_byte(val, 2)));
    assert!(hash(&val) != hash(&zero_byte(val, 3)));

    fn zero_byte(val: u32, byte: usize) -> u32 {
        assert!(byte < 4);
        val & !(0xff << (byte * 8))
    }
}

#[test]
fn test_hash_no_concat_alias() {
    let s = ("aa", "bb");
    let t = ("aabb", "");
    let u = ("a", "abb");

    assert!(s != t && t != u);
    assert!(hash(&s) != hash(&t) && hash(&s) != hash(&u));

    let a = [1u8, 0, 0, 0];
    let v: (&[u8], &[u8], &[u8]) = (&a[0..1], &a[1..3], &a[1..2]);
    let w: (&[u8], &[u8], &[u8]) = (&a[..], &a[0..0], &a[0..0]);

    assert!(v != w);
    assert!(hash(&v) != hash(&w));
}

// unstable
/*#[bench]
fn bench_str_under_8_bytes(b: &mut Bencher) {
    let s = "foo";
    b.bytes=s.len() as u64;
    b.iter(|| {
        hash(&s)
    })
}

#[bench]
fn bench_str_of_8_bytes(b: &mut Bencher) {
    let s = "foobar78";
    b.bytes = s.len() as u64;
    b.iter(|| {
        hash(&s);
    })
}

#[bench]
fn bench_str_over_8_bytes(b: &mut Bencher) {
    let s = "foobarbaz0";
    b.bytes = s.len() as u64;
    b.iter(|| {
        hash(&s)
    })
}

#[bench]
fn bench_long_str(b: &mut Bencher) {
    let s = "Lorem ipsum dolor sit amet, consectetur adipisicing elit, sed do eiusmod tempor \
incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud \
exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute \
irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla \
pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui \
officia deserunt mollit anim id est laborum.";
    b.bytes = s.len() as u64;
    b.iter(|| {
        hash(&s)
    })
}

#[bench]
fn bench_u64(b: &mut Bencher) {
    let u = 16262950014981195938u64;
    b.bytes = 8;
    b.iter(|| {
        hash(&u)
    })
}*/
