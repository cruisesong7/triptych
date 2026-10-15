use cedar_ext_suite::{
    datetime::parser::{datetime_parse, datetime_parse_candidate},
    duration::parser::{duration_parse, duration_parse_candidate},
    ipaddr::{
        ipv4::parser::{ipv4_parse, ipv4_recognize},
        ipv6::parser::{
            ipv6_parse, ipv6_recognize, semantic_hex_sequence_summary_of_span_fast,
            SemanticSpan,
        },
    },
};
use cedar_policy_core::extensions::{
    datetime::{benchmark_parse_datetime, benchmark_parse_duration},
    decimal::benchmark_parse_decimal,
    ipaddr::benchmark_parse_ipaddr,
};
use decimal::parser::{decimal_parse, decimal_parse_candidate};
use std::{hint::black_box, time::Instant};

fn measure_once(iterations: usize, parse: &mut impl FnMut() -> Option<usize>) -> f64 {
    let start = Instant::now();
    let mut checksum = 0usize;
    for index in 0..iterations {
        let parsed = black_box(parse().expect("benchmark input should parse"));
        checksum = checksum.wrapping_add(parsed ^ index);
    }
    black_box(checksum);
    start.elapsed().as_nanos() as f64 / iterations as f64
}

fn measure(label: &str, iterations: usize, mut parse: impl FnMut() -> Option<usize>) -> f64 {
    let _ = measure_once(iterations / 10, &mut parse);
    let mut samples = Vec::with_capacity(9);
    for _ in 0..9 {
        samples.push(measure_once(iterations, &mut parse));
    }
    samples.sort_by(f64::total_cmp);
    let nanoseconds = samples[samples.len() / 2];
    println!("{label:34} {nanoseconds:10.2} ns/parse");
    nanoseconds
}

fn generated_ip(input: &str) -> Option<usize> {
    ipv4_parse(input)
        .map(|parsed| parsed.address as usize)
        .or_else(|| ipv6_parse(input).map(|parsed| parsed.address as usize))
}

fn main() {
    let iterations = 250_000;

    let decimal = black_box("-1234567890.1234");
    measure("Triptych Decimal scan", iterations, || {
        decimal_parse_candidate(decimal).map(|candidate| candidate.end)
    });
    let triptych_decimal = measure("Triptych Decimal full", iterations, || {
        decimal_parse(decimal).map(|_| decimal.len())
    });
    let cedar_decimal = measure("Cedar Decimal production", iterations, || {
        benchmark_parse_decimal(decimal).map(|_| decimal.len())
    });
    println!(
        "  Cedar/Triptych Decimal full: {:.2}x\n",
        cedar_decimal / triptych_decimal
    );

    let duration = black_box("-5d3h2m1s7ms");
    measure("Triptych Duration scan", iterations, || {
        duration_parse_candidate(duration).map(|candidate| candidate.end)
    });
    let triptych_duration = measure("Triptych Duration full", iterations, || {
        duration_parse(duration).map(|value| value as usize)
    });
    let cedar_duration = measure("Cedar Duration production", iterations, || {
        benchmark_parse_duration(duration).map(|_| duration.len())
    });
    println!(
        "  Cedar/Triptych Duration full: {:.2}x\n",
        cedar_duration / triptych_duration
    );

    let datetime = black_box("2024-10-15T11:38:02.101+1134");
    measure("Triptych Datetime scan", iterations, || {
        datetime_parse_candidate(datetime).map(|candidate| candidate.end)
    });
    let triptych_datetime = measure("Triptych Datetime full", iterations, || {
        datetime_parse(datetime).map(|value| value as usize)
    });
    let cedar_datetime = measure("Cedar Datetime production", iterations, || {
        benchmark_parse_datetime(datetime).map(|_| datetime.len())
    });
    println!(
        "  Cedar/Triptych Datetime full: {:.2}x\n",
        cedar_datetime / triptych_datetime
    );

    for input in [
        black_box("127.0.0.1/24"),
        black_box("2001:db8:85a3::8a2e:370:7334/64"),
    ] {
        let label = if input.contains('.') { "IPv4" } else { "IPv6" };
        measure(&format!("Triptych {label} scan"), iterations, || {
            if input.contains('.') {
                ipv4_recognize(input)
            } else {
                ipv6_recognize(input)
            }
        });
        let triptych_family = measure(
            &format!("Triptych {label} family full"),
            iterations,
            || {
                if input.contains('.') {
                    ipv4_parse(input).map(|parsed| parsed.address as usize)
                } else {
                    ipv6_parse(input).map(|parsed| parsed.address as usize)
                }
            },
        );
        let triptych_dispatch = measure(
            &format!("Triptych {label} dispatch full"),
            iterations,
            || generated_ip(input),
        );
        let cedar_ip = measure(&format!("Cedar {label} production"), iterations, || {
            benchmark_parse_ipaddr(input).map(|_| input.len())
        });
        println!(
            "  Cedar/Triptych {label} family: {:.2}x",
            cedar_ip / triptych_family
        );
        println!(
            "  Cedar/Triptych {label} dispatch: {:.2}x\n",
            cedar_ip / triptych_dispatch
        );

        if label == "IPv6" {
            measure("Triptych IPv6 left summary", iterations, || {
                let summary = semantic_hex_sequence_summary_of_span_fast(
                    input,
                    true,
                    SemanticSpan {
                        start: 0,
                        end: 13,
                        count: 0,
                        present: true,
                    },
                );
                summary.value.to_option().map(|value| value as usize)
            });
            measure("Triptych IPv6 right summary", iterations, || {
                let summary = semantic_hex_sequence_summary_of_span_fast(
                    input,
                    true,
                    SemanticSpan {
                        start: 15,
                        end: 28,
                        count: 0,
                        present: true,
                    },
                );
                summary.value.to_option().map(|value| value as usize)
            });
        }
    }
}
