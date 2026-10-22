use cedar_policy_core::extensions::datetime::benchmark_parse_datetime;
use datetime::optimized::DatetimeParser;
use std::hint::black_box;
use std::time::Instant;

fn sample(
    input: &str,
    iterations: usize,
    mut parse: impl FnMut(&str) -> Option<i64>,
) -> (f64, u64) {
    let start = Instant::now();
    let mut checksum = 0u64;
    for _ in 0..iterations {
        let value = black_box(parse(black_box(input)).expect("benchmark input should parse"));
        checksum = checksum.wrapping_add(value as u64);
    }
    (
        start.elapsed().as_nanos() as f64 / iterations as f64,
        checksum,
    )
}

fn report(label: &str, samples: &mut [f64], checksum: u64) -> f64 {
    let rounds = samples
        .iter()
        .map(|sample| format!("{sample:.2}"))
        .collect::<Vec<_>>()
        .join(", ");
    println!("{label:24} rounds [{rounds}]");
    samples.sort_by(f64::total_cmp);
    let median = samples[samples.len() / 2];
    println!(
        "{label:24} {median:8.2} ns/parse ({:.2}–{:.2}, {checksum})",
        samples[0],
        samples[samples.len() - 1],
    );
    median
}

fn main() {
    let input = black_box("2024-01-15T10:30:45.123-0800");
    let iterations = 2_000_000;
    let rounds = 7;
    assert_eq!(
        DatetimeParser::parse(input),
        benchmark_parse_datetime(input)
    );
    let mut verified_samples = Vec::with_capacity(rounds);
    let mut cedar_samples = Vec::with_capacity(rounds);
    let mut checksum = 0u64;
    for round in 0..rounds {
        let (first, second) = if round % 2 == 0 {
            (
                sample(input, iterations, DatetimeParser::parse),
                sample(input, iterations, benchmark_parse_datetime),
            )
        } else {
            let cedar = sample(input, iterations, benchmark_parse_datetime);
            let verified = sample(input, iterations, DatetimeParser::parse);
            (verified, cedar)
        };
        assert_eq!(first.1, second.1);
        verified_samples.push(first.0);
        cedar_samples.push(second.0);
        checksum = first.1;
    }
    let verified = report("Verified external", &mut verified_samples, checksum);
    let cedar = report("Cedar production", &mut cedar_samples, checksum);
    println!("Cedar / verified          {:8.2}x", cedar / verified);
}
