#![cfg_attr(feature = "unstable", feature(error_in_core))]
#![cfg_attr(feature = "unstable", feature(extend_one))]

#![doc = include_str!("../README.md")]

mod smallstr;

pub use smallstr::*;
