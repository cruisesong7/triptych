use vstd::prelude::*;
use vstd::string::StrSliceExecFns;

#[cfg(verus_only)]
use crate::model::*;

verus! {

#[derive(Debug, Structural, Clone, Copy, PartialEq, Eq)]
pub struct IpAddrValue {
    pub family: u8,
    pub address: u128,
    pub prefix: u8,
}

#[cfg(verus_only)]
impl DeepView for IpAddrValue {
    type V = IpAddrSpec;

    open spec fn deep_view(&self) -> IpAddrSpec {
        IpAddrSpec {
            family: self.family as int,
            address: self.address as int,
            prefix: self.prefix as int,
        }
    }
}

pub struct IpAddrParser;

#[inline(always)]
fn ipaddr_is_digit_at(input: &str, index: usize) -> (result: bool)
    requires
        input.is_ascii(),
        index < input@.len(),
    ensures
        result == ipaddr_is_digit(input@[index as int]),
{
    let byte = input.get_ascii(index);
    b'0' <= byte && byte <= b'9'
}

#[inline(always)]
fn ipaddr_hex_value_at(input: &str, index: usize) -> (result: Option<u8>)
    requires
        input.is_ascii(),
        index < input@.len(),
    ensures
        match result {
            Some(value) => {
                ipaddr_hex_value(input@[index as int]) == Some(value as int)
                    && value < 16
            },
            None => ipaddr_hex_value(input@[index as int]).is_none(),
        },
{
    let byte = input.get_ascii(index);
    if b'0' <= byte && byte <= b'9' {
        proof {
            reveal(ipaddr_hex_value);
        }
        Some(byte - b'0')
    } else if b'a' <= byte && byte <= b'f' {
        proof {
            reveal(ipaddr_hex_value);
        }
        Some(byte - b'a' + 10)
    } else if b'A' <= byte && byte <= b'F' {
        proof {
            reveal(ipaddr_hex_value);
        }
        Some(byte - b'A' + 10)
    } else {
        proof {
            reveal(ipaddr_hex_value);
        }
        None
    }
}

fn ipaddr_find_slash_exec(input: &str) -> (result: usize)
    requires
        input.is_ascii(),
    ensures
        result as int == ipaddr_find_slash(input@, 0),
        result <= input@.len(),
{
    let length = input.unicode_len();
    let mut index = 0usize;
    while index < length
        invariant
            input.is_ascii(),
            length == input@.len(),
            index <= length,
            ipaddr_find_slash(input@, 0) == ipaddr_find_slash(input@, index as int),
        decreases length - index,
    {
        if input.get_ascii(index) == b'/' {
            reveal(ipaddr_find_slash);
            return index;
        }
        reveal(ipaddr_find_slash);
        index += 1;
    }
    reveal(ipaddr_find_slash);
    length
}

fn ipaddr_contains_exec(
    input: &str,
    start: usize,
    end: usize,
    character: u8,
) -> (result: bool)
    requires
        input.is_ascii(),
        start <= end <= input@.len(),
    ensures
        result == ipaddr_contains(input@, start as int, end as int, character as char),
{
    let mut index = start;
    while index < end
        invariant
            input.is_ascii(),
            start <= index <= end <= input@.len(),
            ipaddr_contains(input@, start as int, end as int, character as char)
                == ipaddr_contains(input@, index as int, end as int, character as char),
        decreases end - index,
    {
        if input.get_ascii(index) == character {
            reveal(ipaddr_contains);
            return true;
        }
        reveal(ipaddr_contains);
        index += 1;
    }
    reveal(ipaddr_contains);
    false
}

#[inline(always)]
fn ipaddr_push_hex_digit_exec(
    value: u32,
    digits: u8,
    digit: u8,
) -> (result: (u32, u8))
    requires
        digits < 4,
        digit < 16,
        ipaddr_hextet_fits(value as int, digits as int),
    ensures
        result.0 as int == value as int * 16 + digit as int,
        result.1 as int == digits as int + 1,
        ipaddr_hextet_fits(result.0 as int, result.1 as int),
{
    proof {
        reveal(ipaddr_hextet_fits);
        if digits == 0 {
        } else if digits == 1 {
        } else if digits == 2 {
        } else {
            assert(digits == 3);
        }
    }
    (value * 16 + digit as u32, digits + 1)
}

#[inline(always)]
fn ipaddr_append_hextet_exec(
    value: u128,
    count: u8,
    hextet: u32,
) -> (result: (u128, u8))
    requires
        count < 8,
        hextet < 65_536,
        ipaddr_accumulator_fits(value as int, count as int),
    ensures
        result.0 as int == value as int * 65_536 + hextet as int,
        result.1 as int == count as int + 1,
        ipaddr_accumulator_fits(result.0 as int, result.1 as int),
{
    proof {
        reveal(ipaddr_accumulator_fits);
        if count == 0 {
        } else if count == 1 {
        } else if count == 2 {
        } else if count == 3 {
        } else if count == 4 {
        } else if count == 5 {
        } else if count == 6 {
        } else {
            assert(count == 7);
        }
    }
    (value * 65_536 + hextet as u128, count + 1)
}

fn ipaddr_parse_prefix_exec(
    input: &str,
    start: usize,
    end: usize,
    maximum: u8,
) -> (result: Option<u8>)
    requires
        input.is_ascii(),
        start <= end <= input@.len(),
        maximum == 32 || maximum == 128,
    ensures
        match result {
            Some(value) => {
                ipaddr_parse_prefix(input@, start as int, end as int, maximum as int)
                    == Some(value as int)
            },
            None => {
                ipaddr_parse_prefix(input@, start as int, end as int, maximum as int).is_none()
            },
        },
{
    let maximum_length = if maximum == 32 { 2usize } else { 3usize };
    if start == end
        || end - start > maximum_length
        || (input.get_ascii(start) == b'0' && end - start != 1)
    {
        proof {
            reveal(ipaddr_parse_prefix);
        }
        return None;
    }
    let ghost initial = ipaddr_decimal_nat(input@, start as int, end as int, 0);
    proof {
        reveal(ipaddr_parse_prefix);
        assert(
            ipaddr_parse_prefix(input@, start as int, end as int, maximum as int)
                == match initial {
                    Some(value) => if value <= maximum { Some(value) } else { None },
                    None => None,
                }
        );
    }
    let mut index = start;
    let mut value = 0u16;
    while index < end
        invariant
            input.is_ascii(),
            start <= index <= end <= input@.len(),
            end - start <= maximum_length,
            maximum_length <= 3,
            index - start <= maximum_length,
            value <= 999,
            index - start == 0 ==> value == 0,
            index - start == 1 ==> value <= 9,
            index - start == 2 ==> value <= 99,
            index - start == 3 ==> value <= 999,
            ipaddr_decimal_nat(input@, index as int, end as int, value as int) == initial,
            ipaddr_parse_prefix(input@, start as int, end as int, maximum as int)
                == match initial {
                    Some(parsed) => if parsed <= maximum { Some(parsed) } else { None },
                    None => None,
                },
        decreases end - index,
    {
        if !ipaddr_is_digit_at(input, index) {
            proof {
                reveal(ipaddr_decimal_nat);
                assert(initial.is_none());
                assert(initial == None);
                assert(
                    ipaddr_parse_prefix(input@, start as int, end as int, maximum as int).is_none()
                );
            }
            return None;
        }
        let byte = input.get_ascii(index);
        let digit = byte - b'0';
        assert(digit <= 9);
        proof {
            reveal(ipaddr_decimal_nat);
            reveal(ipaddr_digit_value);
            reveal(ipaddr_is_digit);
        }
        value = value * 10 + digit as u16;
        index += 1;
    }
    proof {
        reveal(ipaddr_decimal_nat);
        assert(initial == Some(value as int));
        reveal(ipaddr_parse_prefix);
    }
    if value > maximum as u16 {
        None
    } else {
        Some(value as u8)
    }
}

fn ipaddr_parse_ipv4_exec(
    input: &str,
    end: usize,
) -> (result: Option<u32>)
    requires
        input.is_ascii(),
        0 < end <= input@.len(),
    ensures
        match result {
            Some(value) => {
                ipaddr_ipv4_state(input@, 0, end as int, 0, 0, 0, 0)
                    == Some(value as int)
            },
            None => ipaddr_ipv4_state(input@, 0, end as int, 0, 0, 0, 0).is_none(),
        },
{
    let mut index = 0usize;
    let mut completed_segments = 0u8;
    let mut address = 0u32;
    let mut octet = 0u16;
    let mut digits = 0u8;
    let ghost initial = ipaddr_ipv4_state(input@, 0, end as int, 0, 0, 0, 0);
    while index < end
        invariant
            input.is_ascii(),
            0 <= index <= end <= input@.len(),
            completed_segments <= 3,
            address < 4_294_967_296,
            completed_segments == 0 ==> address == 0,
            completed_segments == 1 ==> address <= 255,
            completed_segments == 2 ==> address <= 65_535,
            completed_segments == 3 ==> address <= 16_777_215,
            octet <= 255,
            digits <= 3,
            initial == ipaddr_ipv4_state(input@, 0, end as int, 0, 0, 0, 0),
            ipaddr_ipv4_state(
                input@,
                index as int,
                end as int,
                completed_segments as int,
                address as int,
                octet as int,
                digits as int,
            ) == initial,
        decreases end - index,
    {
        if ipaddr_is_digit_at(input, index) {
            let byte = input.get_ascii(index);
            let digit = byte - b'0';
            let next_octet = octet * 10 + digit as u16;
            if digits == 3 || (0 < digits && octet == 0) || next_octet > 255 {
                proof {
                    reveal(ipaddr_ipv4_state);
                    reveal(ipaddr_digit_value);
                    reveal(ipaddr_is_digit);
                    assert(initial.is_none());
                    assert(initial == None);
                    assert(ipaddr_ipv4_state(input@, 0, end as int, 0, 0, 0, 0).is_none());
                }
                return None;
            }
            proof {
                reveal(ipaddr_ipv4_state);
                reveal(ipaddr_digit_value);
                reveal(ipaddr_is_digit);
            }
            octet = next_octet;
            digits += 1;
            index += 1;
        } else if input.get_ascii(index) == b'.'
            && 0 < digits
            && completed_segments < 3
        {
            proof {
                reveal(ipaddr_ipv4_state);
                assert(
                    completed_segments == 0
                        || completed_segments == 1
                        || completed_segments == 2
                );
            }
            address = address * 256 + octet as u32;
            completed_segments += 1;
            octet = 0;
            digits = 0;
            index += 1;
        } else {
            proof {
                reveal(ipaddr_ipv4_state);
                assert(initial.is_none());
                assert(initial == None);
                assert(ipaddr_ipv4_state(input@, 0, end as int, 0, 0, 0, 0).is_none());
            }
            return None;
        }
    }
    proof {
        reveal(ipaddr_ipv4_state);
    }
    if completed_segments == 3 && 0 < digits {
        Some(address * 256 + octet as u32)
    } else {
        None
    }
}

fn ipaddr_parse_ipv6_exec(
    input: &str,
    end: usize,
) -> (result: Option<u128>)
    requires
        input.is_ascii(),
        0 < end <= input@.len(),
    ensures
        match result {
            Some(value) => {
                ipaddr_ipv6_state(
                    input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                ) == Some(value as int)
            },
            None => {
                ipaddr_ipv6_state(
                    input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                ).is_none()
            },
        },
{
    let mut index = 0usize;
    let mut left = 0u128;
    let mut right = 0u128;
    let mut left_count = 0u8;
    let mut right_count = 0u8;
    let mut compressed = false;
    let mut hextet = 0u32;
    let mut digits = 0u8;
    let ghost initial =
        ipaddr_ipv6_state(input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0);

    while index < end
        invariant
            input.is_ascii(),
            0 <= index <= end <= input@.len(),
            left_count <= 8,
            right_count <= 8,
            hextet <= 65_535,
            digits <= 4,
            ipaddr_hextet_fits(hextet as int, digits as int),
            ipaddr_accumulator_fits(left as int, left_count as int),
            ipaddr_accumulator_fits(right as int, right_count as int),
            initial == ipaddr_ipv6_state(
                input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
            ),
            ipaddr_ipv6_state(
                input@,
                0,
                index as int,
                end as int,
                left as int,
                right as int,
                left_count as int,
                right_count as int,
                compressed,
                hextet as int,
                digits as int,
            ) == initial,
        decreases end - index,
    {
        match ipaddr_hex_value_at(input, index) {
            Some(digit) => {
                if digits == 4 {
                    proof {
                        reveal(ipaddr_ipv6_state);
                        assert(initial.is_none());
                        assert(initial == None);
                        assert(
                            ipaddr_ipv6_state(
                                input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                            ).is_none()
                        );
                    }
                    return None;
                }
                proof {
                    reveal(ipaddr_ipv6_state);
                }
                let pushed = ipaddr_push_hex_digit_exec(hextet, digits, digit);
                hextet = pushed.0;
                digits = pushed.1;
                index += 1;
            },
            None => {
                if input.get_ascii(index) != b':' {
                    proof {
                        reveal(ipaddr_ipv6_state);
                        assert(initial.is_none());
                        assert(initial == None);
                        assert(
                            ipaddr_ipv6_state(
                                input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                            ).is_none()
                        );
                    }
                    return None;
                }
                if digits == 0 {
                    if index == 0
                        && index + 1 < end
                        && input.get_ascii(index + 1) == b':'
                        && !compressed
                    {
                        proof {
                            reveal(ipaddr_ipv6_state);
                        }
                        compressed = true;
                        index += 2;
                    } else {
                        proof {
                            reveal(ipaddr_ipv6_state);
                            assert(initial.is_none());
                            assert(initial == None);
                            assert(
                                ipaddr_ipv6_state(
                                    input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                                ).is_none()
                            );
                        }
                        return None;
                    }
                } else {
                    if compressed {
                        if right_count == 8 {
                            proof {
                                reveal(ipaddr_ipv6_state);
                                assert(initial.is_none());
                                assert(initial == None);
                                assert(
                                    ipaddr_ipv6_state(
                                        input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                                    ).is_none()
                                );
                            }
                            return None;
                        }
                        let appended = ipaddr_append_hextet_exec(right, right_count, hextet);
                        right = appended.0;
                        right_count = appended.1;
                    } else {
                        if left_count == 8 {
                            proof {
                                reveal(ipaddr_ipv6_state);
                                assert(initial.is_none());
                                assert(initial == None);
                                assert(
                                    ipaddr_ipv6_state(
                                        input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                                    ).is_none()
                                );
                            }
                            return None;
                        }
                        let appended = ipaddr_append_hextet_exec(left, left_count, hextet);
                        left = appended.0;
                        left_count = appended.1;
                    }
                    hextet = 0;
                    digits = 0;
                    if index + 1 < end && input.get_ascii(index + 1) == b':' {
                        if compressed {
                            proof {
                                reveal(ipaddr_ipv6_state);
                                assert(initial.is_none());
                                assert(initial == None);
                                assert(
                                    ipaddr_ipv6_state(
                                        input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                                    ).is_none()
                                );
                            }
                            return None;
                        }
                        proof {
                            reveal(ipaddr_ipv6_state);
                        }
                        compressed = true;
                        index += 2;
                    } else if index + 1 == end {
                        proof {
                            reveal(ipaddr_ipv6_state);
                            assert(initial.is_none());
                            assert(initial == None);
                            assert(
                                ipaddr_ipv6_state(
                                    input@, 0, 0, end as int, 0, 0, 0, 0, false, 0, 0,
                                ).is_none()
                            );
                        }
                        return None;
                    } else {
                        proof {
                            reveal(ipaddr_ipv6_state);
                        }
                        index += 1;
                    }
                }
            },
        }
    }

    if 0 < digits {
        if compressed {
            if right_count == 8 {
                reveal(ipaddr_ipv6_finish);
                return None;
            }
            let appended = ipaddr_append_hextet_exec(right, right_count, hextet);
            right = appended.0;
            right_count = appended.1;
        } else {
            if left_count == 8 {
                reveal(ipaddr_ipv6_finish);
                return None;
            }
            let appended = ipaddr_append_hextet_exec(left, left_count, hextet);
            left = appended.0;
            left_count = appended.1;
        }
    }
    let total_count = left_count + right_count;
    if compressed {
        if total_count >= 8 {
            reveal(ipaddr_ipv6_finish);
            return None;
        }
        let shifts = 8u8 - left_count;
        let mut shifted_left = left;
        let mut shifted = 0u8;
        proof {
            reveal(ipaddr_pow_65536);
            vstd::arithmetic::power::lemma_pow0(65_536);
        }
        while shifted < shifts
            invariant
                shifted <= shifts,
                shifts <= 8,
                left_count + shifts == 8,
                left_count + shifted <= 8,
                ipaddr_accumulator_fits(
                    shifted_left as int,
                    (left_count + shifted) as int,
                ),
                (shifted_left as int)
                    == left as int * ipaddr_pow_65536(shifted as int),
            decreases shifts - shifted,
        {
            let current_count = left_count + shifted;
            let appended = ipaddr_append_hextet_exec(shifted_left, current_count, 0);
            proof {
                broadcast use vstd::arithmetic::mul::group_mul_properties;
                lemma_ipaddr_pow_65536_next(shifted as int);
                assert((shifted as int) + 1 == (shifted + 1) as int);
                assert(
                    ipaddr_pow_65536((shifted + 1) as int)
                        == ipaddr_pow_65536(shifted as int) * 65_536
                );
                assert(
                    appended.0 as int
                        == shifted_left as int * 65_536
                );
            }
            shifted_left = appended.0;
            shifted += 1;
        }
        proof {
            lemma_ipaddr_ipv6_join_fits(
                left as int,
                right as int,
                left_count as int,
                right_count as int,
            );
        }
        let address = shifted_left + right;
        proof {
            reveal(ipaddr_ipv6_finish);
        }
        Some(address)
    } else if total_count == 8 {
        proof {
            reveal(ipaddr_ipv6_finish);
        }
        Some(left)
    } else {
        proof {
            reveal(ipaddr_ipv6_finish);
        }
        None
    }
}

impl IpAddrParser {
    #[inline]
    pub fn parse(input: &str) -> (result: Option<IpAddrValue>)
        ensures
            match result {
                Some(value) => ipaddr_parse_spec(input@) == Some(value.deep_view()),
                None => ipaddr_parse_spec(input@).is_none(),
            },
    {
        if !input.is_ascii() {
            reveal(ipaddr_parse_spec);
            return None;
        }
        let length = input.unicode_len();
        if length == 0 || length > 43 {
            reveal(ipaddr_parse_spec);
            return None;
        }
        let slash = ipaddr_find_slash_exec(input);
        let has_prefix = slash < length;
        let address_end = slash;
        let has_colon = ipaddr_contains_exec(input, 0, address_end, b':');
        let has_dot = ipaddr_contains_exec(input, 0, address_end, b'.');
        if address_end == 0 || (has_colon && has_dot) || (!has_colon && !has_dot) {
            reveal(ipaddr_parse_spec);
            return None;
        }

        if has_dot {
            let prefix = if has_prefix {
                match ipaddr_parse_prefix_exec(input, slash + 1, length, 32) {
                    Some(value) => value,
                    None => {
                        reveal(ipaddr_parse_spec);
                        return None;
                    },
                }
            } else {
                32
            };
            let address = match ipaddr_parse_ipv4_exec(input, address_end) {
                Some(value) => value,
                None => {
                    reveal(ipaddr_parse_spec);
                    return None;
                },
            };
            proof {
                reveal(ipaddr_parse_spec);
            }
            Some(IpAddrValue {
                family: 4,
                address: address as u128,
                prefix,
            })
        } else {
            let prefix = if has_prefix {
                match ipaddr_parse_prefix_exec(input, slash + 1, length, 128) {
                    Some(value) => value,
                    None => {
                        reveal(ipaddr_parse_spec);
                        return None;
                    },
                }
            } else {
                128
            };
            let address = match ipaddr_parse_ipv6_exec(input, address_end) {
                Some(value) => value,
                None => {
                    reveal(ipaddr_parse_spec);
                    return None;
                },
            };
            proof {
                reveal(ipaddr_parse_spec);
            }
            Some(IpAddrValue {
                family: 6,
                address,
                prefix,
            })
        }
    }
}

} // verus!
