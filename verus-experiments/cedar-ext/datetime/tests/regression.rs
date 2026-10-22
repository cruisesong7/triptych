use cedar_policy_core::extensions::datetime::benchmark_parse_datetime;
use datetime::optimized::DatetimeParser;

#[test]
fn specialized_datetime_matches_cedar_corpus() {
    for input in [
        "1970-01-01",
        "1970-01-01T00:00:00Z",
        "2024-01-15T10:30:45.123Z",
        "2024-01-15T10:30:45+0530",
        "2024-01-15T10:30:45.123-0800",
        "0000-01-01",
        "9999-12-31T23:59:59.999Z",
        "2000-02-29",
        "1900-02-28",
        "",
        "1970-1-01",
        "1970-01-1",
        "2024-02-30",
        "1900-02-29",
        "2024-01-15T24:00:00Z",
        "2024-01-15T23:60:00Z",
        "2024-01-15T23:59:60Z",
        "2024-01-15T10:30:45",
        "2024-01-15T10:30:45.12Z",
        "2024-01-15T10:30:45+2400",
        "2024-01-15T10:30:45+0060",
        "2024-01-15T10:30:45+05:30",
        "٢٠٢٤-01-01",
    ] {
        assert_eq!(
            DatetimeParser::parse(input),
            benchmark_parse_datetime(input),
            "input {input:?}"
        );
    }
}

#[test]
fn specialized_datetime_computes_known_epochs() {
    for (input, expected) in [
        ("1970-01-01", 0),
        ("1970-01-01T00:00:00Z", 0),
        ("1970-01-01T01:00:00+0100", 0),
        ("1969-12-31T23:59:59.999Z", -1),
        ("2000-01-01T00:00:00Z", 946_684_800_000),
    ] {
        assert_eq!(DatetimeParser::parse(input), Some(expected));
    }
}

#[test]
fn specialized_datetime_matches_cedar_calendar_grid() {
    for year in [0u32, 1, 1899, 1900, 1969, 1970, 2000, 2024, 9999] {
        for month in 1u32..=12 {
            for day in [1u32, 28, 29, 30, 31] {
                for tail in [
                    String::new(),
                    "T00:00:00Z".to_owned(),
                    "T23:59:59.999Z".to_owned(),
                    "T10:30:45+0530".to_owned(),
                    "T10:30:45.123-0800".to_owned(),
                ] {
                    let input = format!("{year:04}-{month:02}-{day:02}{tail}");
                    assert_eq!(
                        DatetimeParser::parse(&input),
                        benchmark_parse_datetime(&input),
                        "input {input:?}"
                    );
                }
            }
        }
    }
}
