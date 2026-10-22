use std::hint::black_box;
use std::time::Instant;

use triptych_vest_decimal::decimal::{Decimal, DecimalFmt};
use vest_lib::core::exec::Parser;

fn vest_parse_all(input: &[u8]) -> Option<Decimal> {
    let (consumed, value) = DecimalFmt.parse(&input).ok()?;
    (consumed == input.len()).then_some(value)
}

#[derive(Debug)]
struct ManualDecimal {
    negative: bool,
    natural: Vec<u8>,
    fraction: Vec<u8>,
}

fn manual_parse(input: &[u8]) -> Option<ManualDecimal> {
    let mut index = 0;
    let negative = input.first() == Some(&b'-');
    if negative {
        index += 1;
    }

    let natural_start = index;
    while input.get(index).is_some_and(u8::is_ascii_digit) {
        index += 1;
    }
    if index == natural_start || input.get(index) != Some(&b'.') {
        return None;
    }
    let natural = input[natural_start..index].to_vec();
    index += 1;

    let fraction_start = index;
    while input.get(index).is_some_and(u8::is_ascii_digit) {
        index += 1;
    }
    let fraction_len = index - fraction_start;
    if !(1..=4).contains(&fraction_len) || index != input.len() {
        return None;
    }

    Some(ManualDecimal {
        negative,
        natural,
        fraction: input[fraction_start..index].to_vec(),
    })
}

fn time(label: &str, iterations: usize, mut parse: impl FnMut() -> usize) {
    let start = Instant::now();
    let mut checksum = 0;
    for _ in 0..iterations {
        checksum ^= black_box(parse());
    }
    let elapsed = start.elapsed();
    let nanos = elapsed.as_nanos() as f64 / iterations as f64;
    println!("{label:16} {nanos:8.2} ns/parse ({checksum})");
}

fn main() {
    let input = black_box(b"-1234567890.1234".as_slice());
    let iterations = 2_000_000;

    time("Vest", iterations, || {
        let parsed = black_box(vest_parse_all(input).unwrap());
        parsed.natural_following_digits.len()
    });
    time("hand-written", iterations, || {
        let parsed = black_box(manual_parse(input).unwrap());
        usize::from(parsed.negative) + parsed.natural.len() + parsed.fraction.len()
    });
}
