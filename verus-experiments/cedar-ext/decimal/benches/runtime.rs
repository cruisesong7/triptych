use cedar_policy_core::extensions::decimal::benchmark_parse_decimal;
use decimal::optimized::DecimalParser;
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
    let nanoseconds = start.elapsed().as_nanos() as f64 / iterations as f64;
    (nanoseconds, checksum)
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
    let input = black_box("-1234567890.1234");
    let iterations = 5_000_000;
    let rounds = 7;
    assert_eq!(DecimalParser::parse(input), benchmark_parse_decimal(input));
    let mut external_samples = Vec::with_capacity(rounds);
    let mut cedar_samples = Vec::with_capacity(rounds);
    let mut checksum = 0u64;
    for round in 0..rounds {
        let (verified, cedar) = if round % 2 == 0 {
            (
                sample(input, iterations, DecimalParser::parse),
                sample(input, iterations, benchmark_parse_decimal),
            )
        } else {
            let cedar = sample(input, iterations, benchmark_parse_decimal);
            let verified = sample(input, iterations, DecimalParser::parse);
            (verified, cedar)
        };
        assert_eq!(verified.1, cedar.1);
        external_samples.push(verified.0);
        cedar_samples.push(cedar.0);
        checksum = verified.1;
    }
    let external = report("Verified external", &mut external_samples, checksum);
    let cedar = report("Cedar production", &mut cedar_samples, checksum);
    println!("Cedar / verified          {:8.2}x", cedar / external);
}
