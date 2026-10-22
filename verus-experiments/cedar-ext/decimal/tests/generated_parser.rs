use cedar_policy_core::extensions::decimal::benchmark_parse_decimal;
use decimal::optimized::DecimalParser;
use decimal::parser::decimal_parse_candidate;
use decimal::printer::DecimalPrinter;

const VALID_GRAMMAR_CASES: &[&str] = &[
    "1.0",
    "-1.0",
    "123.456",
    "0.1234",
    "-0.0123",
    "55.1",
    "-922337203685477.5808",
    "00.000",
];

const INVALID_GRAMMAR_CASES: &[&str] = &[
    "", "1234", "1.0.", "1.", ".1", "+1.0", "1.a", "-.", "0.12345", "0.00000",
];

#[test]
fn generated_scanner_accepts_decimal_grammar() {
    for input in VALID_GRAMMAR_CASES {
        assert!(decimal_parse_candidate(input).is_some(), "input {input:?}");
    }
}

#[test]
fn generated_scanner_rejects_non_decimal_syntax() {
    for input in INVALID_GRAMMAR_CASES {
        assert!(decimal_parse_candidate(input).is_none(), "input {input:?}");
    }
}

#[test]
fn scanner_accepts_long_leading_zero_runs_without_numeric_overflow() {
    let input = format!("{}1.0", "0".repeat(1024));
    assert!(decimal_parse_candidate(&input).is_some());
}

#[test]
fn grammar_scanning_is_independent_of_semantic_bounds() {
    for input in [
        "1000000000000000.0",
        "922337203685477.5808",
        "-922337203685477.5809",
    ] {
        assert!(
            decimal_parse_candidate(input).is_some(),
            "the grammar accepts {input:?}; Decimal constraints reject it later"
        );
    }
}

#[test]
fn optimized_parser_returns_cedar_scaled_values() {
    for (input, expected) in [
        ("1.0", 10_000),
        ("-1.0", -10_000),
        ("123.456", 1_234_560),
        ("0.1234", 1_234),
        ("-0.0123", -123),
        ("55.1", 551_000),
        ("-922337203685477.5808", i64::MIN),
        ("922337203685477.5807", i64::MAX),
        ("00.000", 0),
    ] {
        assert_eq!(
            DecimalParser::parse(input),
            Some(expected),
            "input {input:?}"
        );
    }
}

#[test]
fn optimized_parser_rejects_syntax_and_semantic_overflow() {
    for input in INVALID_GRAMMAR_CASES.iter().copied().chain([
        "1000000000000000.0",
        "922337203685477.5808",
        "-922337203685477.5809",
        "-922337203685478.0",
    ]) {
        assert_eq!(DecimalParser::parse(input), None, "input {input:?}");
    }
}

#[test]
fn optimized_parser_handles_long_leading_zero_runs() {
    let input = format!("{}1.0", "0".repeat(1024));
    assert_eq!(DecimalParser::parse(&input), Some(10_000));
}

#[test]
fn optimized_parser_matches_cedar_production_parser() {
    for input in VALID_GRAMMAR_CASES
        .iter()
        .copied()
        .chain(INVALID_GRAMMAR_CASES.iter().copied())
        .chain([
            "922337203685477.5807",
            "922337203685477.5808",
            "-922337203685477.5808",
            "-922337203685477.5809",
            "000000000000001.0001",
            "-000000000000001.0001",
        ])
    {
        assert_eq!(
            DecimalParser::parse(input),
            benchmark_parse_decimal(input),
            "input {input:?}"
        );
    }
}

#[test]
fn optimized_parser_matches_cedar_large_structured_corpus() {
    for natural in 0u64..=5_000 {
        for fraction_length in 1u32..=4 {
            let modulus = 10u64.pow(fraction_length);
            let fraction = natural.wrapping_mul(7_919).wrapping_add(104_729) % modulus;
            for sign in ["", "-"] {
                let canonical = format!(
                    "{sign}{natural}.{fraction:0width$}",
                    width = fraction_length as usize
                );
                assert_eq!(
                    DecimalParser::parse(&canonical),
                    benchmark_parse_decimal(&canonical),
                    "structured input {canonical:?}"
                );

                let with_leading_zeros = format!(
                    "{sign}000000{natural}.{fraction:0width$}",
                    width = fraction_length as usize
                );
                assert_eq!(
                    DecimalParser::parse(&with_leading_zeros),
                    benchmark_parse_decimal(&with_leading_zeros),
                    "structured input {with_leading_zeros:?}"
                );
            }
        }
    }
}

#[test]
fn optimized_parser_matches_cedar_deterministic_fuzz_corpus() {
    const ALPHABET: &[u8] = b"0123456789.-+x_";
    let mut state = 0x4d59_5df4_d0f3_3173u64;
    for case in 0..50_000 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let length = (state as usize) % 33;
        let mut input = String::with_capacity(length);
        for _ in 0..length {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            input.push(ALPHABET[(state as usize) % ALPHABET.len()] as char);
        }
        assert_eq!(
            DecimalParser::parse(&input),
            benchmark_parse_decimal(&input),
            "fuzz case {case}, input {input:?}"
        );
    }
}

fn cedar_decimal_to_string(value: i64) -> String {
    let magnitude = i128::from(value).abs();
    format!(
        "{}{}.{:04}",
        if value.is_negative() { "-" } else { "" },
        magnitude / 10_000,
        magnitude % 10_000,
    )
}

#[test]
fn verified_printer_matches_cedar_decimal_display() {
    for value in [
        i64::MIN,
        -12_345_678_901_234_567,
        -10_001,
        -10_000,
        -1,
        0,
        1,
        9_999,
        10_000,
        10_001,
        12_345_678_901_234_567,
        i64::MAX,
    ] {
        assert_eq!(
            DecimalPrinter::to_string(value),
            cedar_decimal_to_string(value),
            "value {value}"
        );
    }
}

#[test]
fn verified_external_parser_printer_roundtrip() {
    for value in [
        i64::MIN,
        -12_345_678_901_234_567,
        -1,
        0,
        1,
        12_345_678_901_234_567,
        i64::MAX,
    ] {
        let encoded = DecimalPrinter::to_string(value);
        assert_eq!(DecimalParser::parse(&encoded), Some(value), "value {value}");
    }
}
