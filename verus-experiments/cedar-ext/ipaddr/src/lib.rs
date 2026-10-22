#![allow(unexpected_cfgs)]

pub mod ipv4;
pub mod ipv6;
#[cfg(verus_only)]
pub mod model;
pub mod optimized;
pub mod printer;
pub mod soundness;
