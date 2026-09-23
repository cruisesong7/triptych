use decimal::parser::decimal_parse_candidate;

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
    "",
    "1234",
    "1.0.",
    "1.",
    ".1",
    "+1.0",
    "1.a",
    "-.",
    "0.12345",
    "0.00000",
];

#[test]
fn generated_scanner_accepts_decimal_grammar() {
    for input in VALID_GRAMMAR_CASES {
        assert!(
            decimal_parse_candidate(input).is_some(),
            "input {input:?}"
        );
    }
}

#[test]
fn generated_scanner_rejects_non_decimal_syntax() {
    for input in INVALID_GRAMMAR_CASES {
        assert!(
            decimal_parse_candidate(input).is_none(),
            "input {input:?}"
        );
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
