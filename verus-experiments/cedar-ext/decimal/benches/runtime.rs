use decimal::parser::decimal_parse_candidate;
use regex::Regex;
use std::hint::black_box;
use std::str::FromStr;
use std::sync::LazyLock;
use std::time::Instant;

const SCALE_DIGITS: u32 = 4;

static DECIMAL_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^(-?\d+)\.(\d+)$").expect("constant regex"));

fn cedar_regex_recognize(input: &str) -> Option<usize> {
    let captures = DECIMAL_REGEX.captures(input)?;
    let fraction = captures.get(2)?.as_str();
    (fraction.len() <= SCALE_DIGITS as usize).then_some(input.len())
}

fn checked_mul_pow(value: i64, exponent: u32) -> Option<i64> {
    value.checked_mul(10_i64.checked_pow(exponent)?)
}

// Mirrors Cedar's private Decimal parsing algorithm for a direct algorithm-level comparison.
fn cedar_style_regex_parse(input: &str) -> Option<i64> {
    let captures = DECIMAL_REGEX.captures(input)?;
    let natural_text = captures.get(1)?.as_str();
    let fraction_text = captures.get(2)?.as_str();
    let natural = checked_mul_pow(i64::from_str(natural_text).ok()?, SCALE_DIGITS)?;
    let fraction_length = u32::try_from(fraction_text.len()).ok()?;
    if SCALE_DIGITS < fraction_length {
        return None;
    }
    let fraction = checked_mul_pow(
        i64::from_str(fraction_text).ok()?,
        SCALE_DIGITS - fraction_length,
    )?;
    if natural_text.starts_with('-') {
        natural.checked_sub(fraction)
    } else {
        natural.checked_add(fraction)
    }
}

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
    let recognition = measure("Cedar regex recognition", iterations, || {
        cedar_regex_recognize(input)
    });
    let full = measure("Cedar-style full parse", iterations, || {
        cedar_style_regex_parse(input).map(|_| input.len())
    });
    println!("vs regex recognition      {:8.2}x", recognition / generated);
    println!("vs Cedar-style full parse {:8.2}x", full / generated);
}
