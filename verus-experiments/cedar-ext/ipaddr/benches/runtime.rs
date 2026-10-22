use cedar_policy_core::extensions::ipaddr::benchmark_parse_ipaddr;
use ipaddr::optimized::IpAddrParser;
use std::hint::black_box;
use std::time::Instant;

fn sample(
    input: &str,
    iterations: usize,
    mut parse: impl FnMut(&str) -> Option<(u8, u128, u8)>,
) -> (f64, u128) {
    let start = Instant::now();
    let mut checksum = 0u128;
    for _ in 0..iterations {
        let (family, address, prefix) =
            black_box(parse(black_box(input)).expect("benchmark input should parse"));
        checksum = checksum.wrapping_add(address ^ ((family as u128) << 120) ^ prefix as u128);
    }
    (
        start.elapsed().as_nanos() as f64 / iterations as f64,
        checksum,
    )
}

fn report(label: &str, samples: &mut [f64], checksum: u128) -> f64 {
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
    let input = black_box("2001:db8:85a3::8a2e:370:7334/64");
    let iterations = 2_000_000;
    let rounds = 7;
    let ours = IpAddrParser::parse(input).map(|value| (value.family, value.address, value.prefix));
    assert_eq!(ours, benchmark_parse_ipaddr(input));
    let mut verified_samples = Vec::with_capacity(rounds);
    let mut cedar_samples = Vec::with_capacity(rounds);
    let mut checksum = 0u128;
    for round in 0..rounds {
        let (first, second) = if round % 2 == 0 {
            (
                sample(input, iterations, |input| {
                    IpAddrParser::parse(input)
                        .map(|value| (value.family, value.address, value.prefix))
                }),
                sample(input, iterations, benchmark_parse_ipaddr),
            )
        } else {
            let cedar = sample(input, iterations, benchmark_parse_ipaddr);
            let verified = sample(input, iterations, |input| {
                IpAddrParser::parse(input).map(|value| (value.family, value.address, value.prefix))
            });
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
