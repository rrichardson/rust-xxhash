#![macro_use]

// read an integer, advance the pointer by the appropriate amount,
// decrease some counter and do the endian dance
#[macro_export]
macro_rules! read_ptr(($p:ident, $rem:ident, $size:ty) => ({
    #[allow(unused_assignments)]
    use std::mem;
    let mut dp: *const $size = mem::transmute($p);
    let data: $size = *dp;
    dp = dp.offset(1);
    $rem -= mem::size_of::<$size>();
    $p = mem::transmute(dp);
    data.to_le()
}));
