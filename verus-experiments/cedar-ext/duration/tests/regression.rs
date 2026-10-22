use cedar_policy_core::extensions::datetime::benchmark_parse_duration;
use duration::optimized::DurationParser;
use duration::printer::DurationPrinter;

#[test]
fn specialized_duration_matches_cedar_corpus() {
    for input in [
        "0ms",
        "1d",
        "2h",
        "3m",
        "4s",
        "5ms",
        "1d2h3m4s5ms",
        "-1d2h3m4s5ms",
        "0001d0002h",
        "9223372036854775807ms",
        "-9223372036854775808ms",
        "",
        "-",
        "+1s",
        "1",
        "1d1d",
        "1h1d",
        "1ms1s",
        "1m1ms1s",
        "18446744073709551616ms",
        "9223372036854775808ms",
        "-9223372036854775809ms",
        "106751991168d",
        "1µs",
    ] {
        assert_eq!(
            DurationParser::parse(input),
            benchmark_parse_duration(input),
            "input {input:?}"
        );
    }
}

#[test]
fn specialized_duration_computes_expected_values() {
    for (input, expected) in [
        ("1d2h30m", 95_400_000),
        ("-4s200ms", -4_200),
        ("0d0h0m0s0ms", 0),
        ("-0ms", 0),
        ("9223372036854775807ms", i64::MAX),
        ("-9223372036854775808ms", i64::MIN),
    ] {
        assert_eq!(DurationParser::parse(input), Some(expected));
    }
}

#[test]
fn specialized_duration_matches_cedar_generated_cases() {
    let quantities = [0u64, 1, 9, 10, 255, 999, 65_535, 1_000_000];
    for quantity in quantities {
        for suffix in ["d", "h", "m", "s", "ms"] {
            let input = format!("{quantity}{suffix}");
            assert_eq!(
                DurationParser::parse(&input),
                benchmark_parse_duration(&input),
                "input {input:?}"
            );
            let negative = format!("-{input}");
            assert_eq!(
                DurationParser::parse(&negative),
                benchmark_parse_duration(&negative),
                "input {negative:?}"
            );
        }
    }

    for days in [0u64, 1, 99] {
        for hours in [0u64, 1, 23] {
            for minutes in [0u64, 1, 59] {
                let input = format!("{days}d{hours}h{minutes}m7s8ms");
                assert_eq!(
                    DurationParser::parse(&input),
                    benchmark_parse_duration(&input),
                    "input {input:?}"
                );
            }
        }
    }
}

#[test]
fn specialized_duration_printer_matches_cedar_display() {
    for value in [i64::MIN, -86_400_001, -1, 0, 1, 86_400_001, i64::MAX] {
        assert_eq!(DurationPrinter::to_string(value), format!("{value}ms"));
    }
}
