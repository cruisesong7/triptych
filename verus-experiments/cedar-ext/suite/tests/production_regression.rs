use cedar_ext_suite::{
    datetime::parser::{datetime_parse, datetime_parse_candidate},
    duration::parser::{duration_parse, duration_parse_candidate},
    ipaddr::{
        ipv4::parser::{ipv4_parse, ipv4_parse_candidate},
        ipv6::parser::{ipv6_parse, ipv6_parse_candidate},
    },
};
use cedar_policy_core::extensions::{
    datetime::{benchmark_parse_datetime, benchmark_parse_duration},
    ipaddr::benchmark_parse_ipaddr,
};
use decimal::parser::decimal_parse;

fn generated_ip(input: &str) -> Option<(u8, u128, u8)> {
    ipv4_parse(input)
        .map(|parsed| (parsed.family, parsed.address, parsed.prefix))
        .or_else(|| {
            ipv6_parse(input).map(|parsed| (parsed.family, parsed.address, parsed.prefix))
        })
}

fn generated_ip_candidate(input: &str) -> bool {
    ipv4_parse_candidate(input).is_some() || ipv6_parse_candidate(input).is_some()
}

// Copied from cedar-policy-core/src/extensions/datetime.rs::tests::test_parse_pos.
const DATETIME_VALID: &[&str] = &[
    "2024-10-15",
    "2024-10-15T11:38:02Z",
    "2024-10-15T11:38:02.101Z",
    "2024-10-15T11:38:02.101+1134",
    "2024-10-15T11:38:02.101-1134",
    "2024-10-15T11:38:02+1134",
    "2024-10-15T11:38:02-1134",
    "2024-10-15T23:59:00+2359",
    "2024-10-15T00:00:00-2359",
];

// The first lexical rejection block in
// cedar-policy-core/src/extensions/datetime.rs::tests::test_parse_neg.
const DATETIME_LEXICALLY_INVALID: &[&str] = &[
    "",
    "a",
    "-",
    "-1",
    "11-12-13",
    "1111-1x-20",
    "2024-10-15Z",
    "2024-10-15T11:38:02ZZ",
    "0000-0a-01",
    "10000-01-01",
    "10000-01-01T00:00:00Z",
    "2024-01-01T",
    "2024-01-01Ta",
    "2024-01-01T01:",
    "2024-01-01T01:02",
    "2024-01-01T01:02:0b",
    "2024-01-01T01::02:03",
    "2024-01-01T01::02::03",
    "2024-01-01T00:00:00",
    "2024-01-01T00:00:00ZZ",
    "2024-01-01T00:00:00.0001Z",
    "2024-01-01T00:00:00.001+00000",
];

// Cedar rejects these in test_parse_neg after their lexical shape has matched.
const DATETIME_SEMANTICALLY_INVALID: &[&str] = &[
    "2024-00-01",
    "2024-01-00",
    "2024-02-30",
    "2025-02-29",
    "2024-20-01",
    "2024-01-32",
    "2024-04-31",
    "2024-01-01T31:02:03Z",
    "2024-01-01T01:60:03Z",
    "2016-12-31T23:59:60Z",
    "2016-12-31T00:00:00+1160",
    "2016-12-31T00:00:00+2400",
];

// Copied from cedar-policy-core/src/extensions/datetime.rs::tests::parse_duration_pos.
const DURATION_VALID: &[&str] = &["1h", "-10h", "5d3ms", "-3h5m"];

// Copied from cedar-policy-core/src/extensions/datetime.rs::tests::parse_duration_neg.
const DURATION_LEXICALLY_INVALID: &[&str] = &[
    "a",
    "-1",
    "➖1ms",
    "11dd",
    "00000mm",
    "-d",
    "-h",
    "-1hh",
    "-h2d",
    "-ms",
    "1ms1s",
    "1ms1m",
    "1ms1h",
    "0ms1d",
    "1s1m",
    "1s1h",
    "0s0d",
    "0m0h",
    "0m0d",
    "1h1d",
    "1ms1m1d",
];

// The all-optional Components production accepts these shapes; Cedar's nonempty semantic
// constraint rejects them in parse_duration_neg.
const DURATION_SEMANTICALLY_INVALID: &[&str] = &["", "-"];

// Copied from cedar-policy-core/src/extensions/ipaddr.rs::tests::ip_range_creation and
// the neighboring creation/equality tests.
const IP_VALID: &[(&str, u8)] = &[
    ("127.0.0.1", 4),
    ("192.168.0.1", 4),
    ("8.8.8.8", 4),
    ("127.0.0.1/0", 4),
    ("127.0.0.1/24", 4),
    ("127.0.0.1/32", 4),
    ("::1", 6),
    ("ffee::11", 6),
    ("ffee::/0", 6),
    ("ffee::/64", 6),
    ("ffee::/128", 6),
];

// Lexical failures copied from ip_range_creation.
const IP_LEXICALLY_INVALID: &[&str] = &[
    "127.0.0.1/8/24",
    "fee::/64::1",
    "ffee::/+1",
    "ffee::/1234",
];

// These have the grammar shape of an address/prefix but violate Cedar's semantic constraints.
const IP_SEMANTICALLY_INVALID: &[&str] =
    &["172.0.0.1/64", "ffee::/132", "ffee::/01"];

#[test]
fn datetime_generated_parser_matches_cedar_production_values() {
    for input in DATETIME_VALID
        .iter()
        .chain(DATETIME_LEXICALLY_INVALID)
        .chain(DATETIME_SEMANTICALLY_INVALID)
    {
        assert_eq!(
            datetime_parse(input),
            benchmark_parse_datetime(input),
            "input {input:?}"
        );
    }
}

#[test]
fn datetime_semantic_rejections_are_not_misreported_as_grammar_failures() {
    for input in DATETIME_SEMANTICALLY_INVALID {
        assert!(datetime_parse(input).is_none(), "Triptych accepted {input:?}");
        assert!(
            datetime_parse_candidate(input).is_some(),
            "expected {input:?} to reach the generated semantic stage"
        );
    }
}

#[test]
fn duration_generated_parser_matches_cedar_production_values() {
    for input in DURATION_VALID
        .iter()
        .chain(DURATION_LEXICALLY_INVALID)
        .chain(DURATION_SEMANTICALLY_INVALID)
    {
        assert_eq!(
            duration_parse(input),
            benchmark_parse_duration(input),
            "input {input:?}"
        );
    }
}

#[test]
fn duration_semantic_rejections_are_not_misreported_as_grammar_failures() {
    for input in DURATION_SEMANTICALLY_INVALID {
        assert!(duration_parse(input).is_none(), "Triptych accepted {input:?}");
        assert!(
            duration_parse_candidate(input).is_some(),
            "expected {input:?} to reach the generated semantic stage"
        );
    }
}

#[test]
fn decimal_generated_semantic_parser_matches_cedar_production_values() {
    // Copied from cedar-policy-core/src/extensions/decimal.rs::tests::decimal_creation.
    for input in [
        "1.0",
        "-1.0",
        "123.456",
        "0.1234",
        "-0.0123",
        "55.1",
        "-922337203685477.5808",
        "00.000",
    ] {
        assert_eq!(
            decimal_parse(input),
            cedar_policy_core::extensions::decimal::benchmark_parse_decimal(input),
            "input {input:?}"
        );
    }

    for input in [
        "1234",
        "1.0.",
        "1.",
        ".1",
        "1.a",
        "-.",
        "1000000000000000.0",
        "922337203685477.5808",
        "-922337203685477.5809",
        "-922337203685478.0",
        "0.12345",
        "0.00000",
    ] {
        assert_eq!(
            decimal_parse(input),
            cedar_policy_core::extensions::decimal::benchmark_parse_decimal(input),
            "input {input:?}"
        );
    }
}

#[test]
fn ip_generated_parsers_match_cedar_production_values() {
    for (input, _) in IP_VALID {
        assert_eq!(
            generated_ip(input),
            benchmark_parse_ipaddr(input),
            "input {input:?}"
        );
    }

    for input in IP_LEXICALLY_INVALID
        .iter()
        .chain(IP_SEMANTICALLY_INVALID)
    {
        assert_eq!(
            generated_ip(input),
            benchmark_parse_ipaddr(input),
            "input {input:?}"
        );
    }
}

#[test]
fn ip_semantic_rejections_are_not_misreported_as_grammar_failures() {
    for input in IP_SEMANTICALLY_INVALID {
        assert!(generated_ip(input).is_none(), "Triptych accepted {input:?}");
        assert!(
            generated_ip_candidate(input),
            "expected {input:?} to reach the generated semantic stage"
        );
    }
}
