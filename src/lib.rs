#![cfg_attr(feature = "unstable", feature(error_in_core))]
#![cfg_attr(feature = "unstable", feature(extend_one))]
#![cfg_attr(not(feature = "std"), no_std)]

#![doc = include_str!("../README.md")]

mod smallstr;

pub use smallstr::*;
