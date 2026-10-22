use cedar_policy_core::extensions::ipaddr::benchmark_parse_ipaddr;
use ipaddr::optimized::{IpAddrParser, IpAddrValue};

fn cedar(input: &str) -> Option<IpAddrValue> {
    benchmark_parse_ipaddr(input).map(|(family, address, prefix)| IpAddrValue {
        family,
        address,
        prefix,
    })
}

#[test]
fn specialized_ipaddr_matches_cedar_corpus() {
    for input in [
        "0.0.0.0",
        "127.0.0.1",
        "192.168.1.100/24",
        "255.255.255.255/32",
        "1:2:3:4:5:6:7:8",
        "2001:db8::1",
        "::",
        "::1/128",
        "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/0",
        "",
        "1.2.3",
        "1.2.3.4.5",
        "01.2.3.4",
        "256.0.0.1",
        "127.0.0.1/33",
        "127.0.0.1/01",
        ":",
        "1:2:3:4:5:6:7",
        "1:2:3:4:5:6:7:8:9",
        "1:2:3:4:5:6:7::8",
        "1::2::3",
        "::1/129",
        "::1/01",
        "::ffff:192.168.0.1",
        "2001:db8::1/",
        "2001:db8::1//64",
        "gggg::1",
    ] {
        assert_eq!(IpAddrParser::parse(input), cedar(input), "input {input:?}");
    }
}

#[test]
fn specialized_ipaddr_computes_expected_values() {
    assert_eq!(
        IpAddrParser::parse("192.168.1.1/24"),
        Some(IpAddrValue {
            family: 4,
            address: 0xc0a8_0101,
            prefix: 24,
        })
    );
    assert_eq!(
        IpAddrParser::parse("2001:db8::1"),
        Some(IpAddrValue {
            family: 6,
            address: 0x2001_0db8_0000_0000_0000_0000_0000_0001,
            prefix: 128,
        })
    );
}

#[test]
fn specialized_ipaddr_matches_cedar_generated_cases() {
    let octets = [0u16, 1, 9, 10, 127, 128, 254, 255, 256];
    for first in octets {
        for second in [0u16, 1, 255, 256] {
            for fourth in [0u16, 1, 255, 256] {
                for suffix in ["", "/0", "/24", "/32", "/33", "/01"] {
                    let input = format!("{first}.{second}.99.{fourth}{suffix}");
                    assert_eq!(
                        IpAddrParser::parse(&input),
                        cedar(&input),
                        "input {input:?}"
                    );
                }
            }
        }
    }

    for input in [
        "0:0:0:0:0:0:0:0",
        "1:2:3:4:5:6:7:8/64",
        "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff",
        "::",
        "::1",
        "1::",
        "1:2::7:8",
        "1:2:3:4:5:6::8",
        "1:2:3:4:5:6:7::",
        "::ffff:ffff:ffff:ffff:ffff:ffff:ffff",
        "1:2:3:4:5:6:7::8",
        "1:2:3:4:5:6:7",
        "1:2:3:4:5:6:7:8:9",
        "12345::1",
        "::1/0",
        "::1/128",
        "::1/129",
        "::1/01",
    ] {
        assert_eq!(IpAddrParser::parse(input), cedar(input), "input {input:?}");
    }
}
