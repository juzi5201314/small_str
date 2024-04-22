#![feature(test)]

use small_str::{SmallStr, SmallString};
use test::{black_box, Bencher};

extern crate test;

const TEST_STR: &str = "Hello, world!";

#[bench]
pub fn alloc_string(b: &mut Bencher) {
    b.iter(|| {
        let _ = black_box(String::from(TEST_STR));
    })
}

#[bench]
pub fn alloc_smallstr(b: &mut Bencher) {
    b.iter(|| {
        let _ = black_box(SmallString::from(TEST_STR));
    })
}

#[bench]
pub fn alloc_smallstr_spilled(b: &mut Bencher) {
    b.iter(|| {
        let _ = black_box(SmallStr::<6>::from(TEST_STR));
    })
}

#[bench]
pub fn clone_string(b: &mut Bencher) {
    let s = String::from(TEST_STR);
    b.iter(|| {
        let _ = black_box(s.clone());
    })
}

#[bench]
pub fn clone_smallstr(b: &mut Bencher) {
    let s = SmallString::from(TEST_STR);
    b.iter(|| {
        let _ = black_box(s.clone());
    })
}

#[bench]
pub fn clone_smallstr_spilled(b: &mut Bencher) {
    let s = SmallStr::<6>::from(TEST_STR);
    b.iter(|| {
        let _ = black_box(s.clone());
    })
}
