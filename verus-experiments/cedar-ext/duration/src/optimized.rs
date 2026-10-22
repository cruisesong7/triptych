// Optimized external parser proved against Triptych's generated Verus specification.

use vstd::prelude::*;
use vstd::string::StrSliceExecFns;

#[cfg(verus_only)]
use crate::model::{
    duration_digit_value, duration_is_digit, duration_parse_spec, duration_parse_state,
    duration_unit_length, duration_unit_multiplier, duration_unit_rank,
};
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::utf8::is_ascii_chars;

verus! {

pub struct DurationParser;

#[inline(always)]
fn duration_is_digit_at(input: &str, index: usize) -> (result: bool)
    requires
        input.is_ascii(),
        index < input@.len(),
    ensures
        result == duration_is_digit(input@[index as int]),
{
    let byte = input.get_ascii(index);
    byte >= b'0' && byte <= b'9'
}

impl DurationParser {
    #[inline]
    pub fn parse(input: &str) -> (result: Option<i64>)
        ensures
            match result {
                Some(value) => duration_parse_spec(input@) == Some(value as int),
                None => duration_parse_spec(input@).is_none(),
            },
    {
        if !input.is_ascii() {
            proof {
                reveal(duration_parse_spec);
                reveal(duration_parse_state);
                reveal(duration_is_digit);
            }
            return None;
        }
        let length = input.unicode_len();
        if length == 0 {
            reveal(duration_parse_spec);
            return None;
        }
        let negative = input.get_ascii(0) == b'-';
        assert(negative == (input@[0] == '-'));
        let start = if negative { 1usize } else { 0usize };
        if start == length {
            reveal(duration_parse_spec);
            return None;
        }
        let limit = if negative {
            9_223_372_036_854_775_808u128
        } else {
            9_223_372_036_854_775_807u128
        };
        let mut index = start;
        let mut previous_rank = -1i8;
        let mut total = 0u128;
        let mut quantity = 0u64;
        let mut in_digits = false;
        let ghost initial =
            duration_parse_state(input@, start as int, -1, 0, limit as int, 0, false);
        proof {
            reveal(duration_parse_spec);
            assert(
                duration_parse_spec(input@)
                    == match initial {
                        Some(value) => if negative { Some(-value) } else { Some(value) },
                        None => None,
                    }
            );
        }

        while index < length
            invariant
                input.is_ascii(),
                0 < length == input@.len(),
                start <= index <= length,
                -1 <= previous_rank <= 4,
                0 <= total <= limit,
                quantity <= 9_223_372_036_854_775_808,
                limit == 9_223_372_036_854_775_807
                    || limit == 9_223_372_036_854_775_808,
                duration_parse_state(
                    input@,
                    index as int,
                    previous_rank as int,
                    total as int,
                    limit as int,
                    quantity as int,
                    in_digits,
                ) == initial,
                duration_parse_spec(input@)
                    == match initial {
                        Some(value) => if negative { Some(-value) } else { Some(value) },
                        None => None,
                    },
            decreases length - index,
        {
            if duration_is_digit_at(input, index) {
                let byte = input.get_ascii(index);
                let digit = byte - b'0';
                assert(digit <= 9);
                if quantity > 922_337_203_685_477_580 {
                    proof {
                        reveal(duration_parse_state);
                        reveal(duration_digit_value);
                        reveal(duration_is_digit);
                        assert(initial.is_none());
                        assert(initial == None);
                        assert(duration_parse_spec(input@).is_none());
                    }
                    return None;
                }
                let next_quantity = quantity * 10 + digit as u64;
                if next_quantity > 9_223_372_036_854_775_808u64 {
                    proof {
                        reveal(duration_parse_state);
                        reveal(duration_digit_value);
                        reveal(duration_is_digit);
                        assert(initial.is_none());
                        assert(initial == None);
                        assert(duration_parse_spec(input@).is_none());
                    }
                    return None;
                }
                proof {
                    reveal(duration_parse_state);
                    reveal(duration_digit_value);
                    reveal(duration_is_digit);
                }
                quantity = next_quantity;
                in_digits = true;
                index += 1;
                continue;
            }

            if !in_digits {
                proof {
                    reveal(duration_parse_state);
                    assert(initial.is_none());
                    assert(initial == None);
                    assert(duration_parse_spec(input@).is_none());
                }
                return None;
            }

            let unit = input.get_ascii(index);
            let (rank, multiplier, suffix_length) =
                if unit == b'd' {
                    (0i8, 86_400_000u64, 1usize)
                } else if unit == b'h' {
                    (1i8, 3_600_000u64, 1usize)
                } else if unit == b'm'
                    && index + 1 < length
                    && input.get_ascii(index + 1) == b's'
                {
                    (4i8, 1u64, 2usize)
                } else if unit == b'm' {
                    (2i8, 60_000u64, 1usize)
                } else if unit == b's' {
                    (3i8, 1_000u64, 1usize)
                } else {
                    proof {
                        reveal(duration_parse_state);
                        reveal(duration_unit_rank);
                        reveal(duration_unit_length);
                        assert(initial.is_none());
                        assert(initial == None);
                        assert(duration_parse_spec(input@).is_none());
                    }
                    return None;
                };
            let next = index + suffix_length;
            assert(next <= length);
            if rank <= previous_rank {
                proof {
                    reveal(duration_parse_state);
                    reveal(duration_unit_rank);
                    reveal(duration_unit_length);
                    assert(initial.is_none());
                    assert(initial == None);
                    assert(duration_parse_spec(input@).is_none());
                }
                return None;
            }

            let contribution = quantity as u128 * multiplier as u128;
            assert(contribution < 1_000_000_000_000_000_000_000_000_000u128);
            if contribution > limit - total {
                proof {
                    reveal(duration_parse_state);
                    reveal(duration_unit_rank);
                    reveal(duration_unit_length);
                    reveal(duration_unit_multiplier);
                    assert(initial.is_none());
                    assert(initial == None);
                    assert(duration_parse_spec(input@).is_none());
                }
                return None;
            }
            proof {
                reveal(duration_parse_state);
                reveal(duration_unit_rank);
                reveal(duration_unit_length);
                reveal(duration_unit_multiplier);
            }
            total += contribution;
            previous_rank = rank;
            quantity = 0;
            in_digits = false;
            index = next;
        }

        if in_digits || previous_rank < 0 {
            proof {
                reveal(duration_parse_state);
                assert(initial.is_none());
                assert(initial == None);
                assert(duration_parse_spec(input@).is_none());
            }
            return None;
        }
        proof {
            reveal(duration_parse_state);
            assert(initial == Some(total as int));
        }
        let magnitude = total as u64;
        if negative {
            if magnitude == 9_223_372_036_854_775_808u64 {
                Some(i64::MIN)
            } else {
                Some(-(magnitude as i64))
            }
        } else {
            Some(magnitude as i64)
        }
    }
}

} // verus!
