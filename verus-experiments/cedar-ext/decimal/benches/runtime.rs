use cedar_policy_core::extensions::decimal::benchmark_parse_decimal;
use decimal::parser::{decimal_parse, decimal_parse_candidate};
use std::hint::black_box;
use std::time::Instant;

fn measure(label: &str, iterations: usize, mut parse: impl FnMut() -> Option<usize>) -> f64 {
    let start = Instant::now();
    let mut checksum = 0usize;
    for _ in 0..iterations {
        checksum ^= black_box(parse().expect("benchmark input should parse"));
    }
    let nanoseconds = start.elapsed().as_nanos() as f64 / iterations as f64;
    println!("{label:24} {nanoseconds:8.2} ns/parse ({checksum})");
    nanoseconds
}

fn main() {
    let input = black_box("-1234567890.1234");
    let iterations = 5_000_000;
    let generated = measure("Triptych ScanPlan", iterations, || {
        decimal_parse_candidate(input).map(|candidate| candidate.end)
    });
    let generated_full = measure("Triptych full parse", iterations, || {
        decimal_parse(input).map(|_| input.len())
    });
    let cedar = measure("Cedar production parse", iterations, || {
        benchmark_parse_decimal(input).map(|_| input.len())
    });
    println!("Cedar vs Triptych scanner {:8.2}x", cedar / generated);
    println!("Cedar vs Triptych full    {:8.2}x", cedar / generated_full);
}
