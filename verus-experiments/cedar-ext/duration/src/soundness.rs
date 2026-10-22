// Implementation of Triptych's generated external-parser contract.

#[cfg(verus_only)]
use vstd::assert_seqs_equal;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::utf8::is_ascii_chars;

use crate::contract::DurationExternalParserContract;
#[cfg(verus_only)]
use crate::contract::{duration_has_result, duration_matches_result};
#[cfg(verus_only)]
use crate::model::{
    duration_digit_value, duration_is_digit, duration_parse_spec, duration_parse_state,
    duration_unit_length, duration_unit_multiplier, duration_unit_rank,
};
use crate::optimized::DurationParser;
#[cfg(verus_only)]
use crate::printer::{
    duration_canonical_characters, duration_natural_characters,
    duration_natural_characters_properties,
};
#[cfg(verus_only)]
use crate::spec::*;

verus! {

pub struct DurationParts {
    pub d_days: Seq<char>,
    pub d_hours: Seq<char>,
    pub d_minutes: Seq<char>,
    pub d_seconds: Seq<char>,
    pub d_millis: Seq<char>,
}

pub open spec fn duration_part_text(digits: Seq<char>, rank: int) -> Seq<char> {
    if digits.len() == 0 {
        Seq::<char>::empty()
    } else if rank == 0 {
        digits + seq!['d']
    } else if rank == 1 {
        digits + seq!['h']
    } else if rank == 2 {
        digits + seq!['m']
    } else if rank == 3 {
        digits + seq!['s']
    } else {
        digits + seq!['m', 's']
    }
}

pub open spec fn duration_parts_text(parts: DurationParts) -> Seq<char> {
    duration_part_text(parts.d_days, 0)
        + duration_part_text(parts.d_hours, 1)
        + duration_part_text(parts.d_minutes, 2)
        + duration_part_text(parts.d_seconds, 3)
        + duration_part_text(parts.d_millis, 4)
}

pub open spec fn duration_parts_value(parts: DurationParts) -> int {
    triptych_nat_of(parts.d_days) * 86_400_000
        + triptych_nat_of(parts.d_hours) * 3_600_000
        + triptych_nat_of(parts.d_minutes) * 60_000
        + triptych_nat_of(parts.d_seconds) * 1_000
        + triptych_nat_of(parts.d_millis)
}

pub open spec fn duration_digits_wf(digits: Seq<char>) -> bool {
    digits.len() == 0
        || (1 <= digits.len()
            && forall|index: int| 0 <= index < digits.len() ==>
                #[trigger] triptych_is_digit(digits[index]))
}

pub open spec fn duration_parts_after(parts: DurationParts, previous_rank: int) -> bool {
    duration_digits_wf(parts.d_days)
        && duration_digits_wf(parts.d_hours)
        && duration_digits_wf(parts.d_minutes)
        && duration_digits_wf(parts.d_seconds)
        && duration_digits_wf(parts.d_millis)
        && (previous_rank < 0 || parts.d_days.len() == 0)
        && (previous_rank < 1 || parts.d_hours.len() == 0)
        && (previous_rank < 2 || parts.d_minutes.len() == 0)
        && (previous_rank < 3 || parts.d_seconds.len() == 0)
        && (previous_rank < 4 || parts.d_millis.len() == 0)
}

pub proof fn duration_triptych_nat_of_from_push_digit(
    characters: Seq<char>,
    index: int,
    accumulator: int,
    digit: char,
)
    requires
        0 <= index <= characters.len(),
        triptych_is_digit(digit),
    ensures
        triptych_nat_of_from(
            characters.push(digit),
            index,
            accumulator,
        ) == triptych_nat_of_from(characters, index, accumulator) * 10
            + (digit as int - TRIPTYCH_ZERO as int),
    decreases characters.len() - index,
{
    if index < characters.len() {
        assert(characters.push(digit)[index] == characters[index]);
        duration_triptych_nat_of_from_push_digit(
            characters,
            index + 1,
            accumulator * 10
                + if (characters[index] as int) < (TRIPTYCH_ZERO as int) {
                    0
                } else {
                    (characters[index] as int) - (TRIPTYCH_ZERO as int)
                },
            digit,
        );
        reveal(triptych_nat_of_from);
    } else {
        assert(index == characters.len());
        assert(characters.push(digit)[index] == digit);
        reveal(triptych_is_digit);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
}

pub proof fn duration_triptych_nat_of_push_digit(
    characters: Seq<char>,
    digit: char,
)
    requires
        triptych_is_digit(digit),
    ensures
        triptych_nat_of(characters.push(digit))
            == triptych_nat_of(characters) * 10
                + (digit as int - TRIPTYCH_ZERO as int),
{
    duration_triptych_nat_of_from_push_digit(characters, 0, 0, digit);
    reveal(triptych_nat_of);
}

pub proof fn duration_nat_of_subrange_nonnegative(
    input: Seq<char>,
    start: int,
    end: int,
)
    requires
        0 <= start <= end <= input.len(),
        forall|position: int| start <= position < end ==>
            #[trigger] triptych_is_digit(input[position]),
    ensures
        0 <= triptych_nat_of(input.subrange(start, end)),
    decreases end - start,
{
    if start == end {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    } else {
        let prefix = input.subrange(start, end - 1);
        let digits = input.subrange(start, end);
        duration_nat_of_subrange_nonnegative(input, start, end - 1);
        assert(triptych_is_digit(input[end - 1]));
        assert(digits == prefix.push(input[end - 1])) by {
            assert_seqs_equal!(digits == prefix.push(input[end - 1]));
        }
        duration_triptych_nat_of_push_digit(prefix, input[end - 1]);
        reveal(triptych_is_digit);
    }
}

pub proof fn duration_nat_of_subrange_prefix_le(
    input: Seq<char>,
    start: int,
    middle: int,
    end: int,
)
    requires
        0 <= start <= middle <= end <= input.len(),
        forall|position: int| start <= position < end ==>
            #[trigger] triptych_is_digit(input[position]),
    ensures
        triptych_nat_of(input.subrange(start, middle))
            <= triptych_nat_of(input.subrange(start, end)),
    decreases end - middle,
{
    if middle < end {
        let prefix = input.subrange(start, middle);
        let next_prefix = input.subrange(start, middle + 1);
        duration_nat_of_subrange_nonnegative(input, start, middle);
        assert(triptych_is_digit(input[middle]));
        assert(next_prefix == prefix.push(input[middle])) by {
            assert_seqs_equal!(next_prefix == prefix.push(input[middle]));
        }
        duration_triptych_nat_of_push_digit(prefix, input[middle]);
        reveal(triptych_is_digit);
        assert(triptych_nat_of(prefix) <= triptych_nat_of(next_prefix));
        duration_nat_of_subrange_prefix_le(input, start, middle + 1, end);
    }
}

pub proof fn duration_parse_state_complete_digits(
    input: Seq<char>,
    component_start: int,
    index: int,
    end: int,
    previous_rank: int,
    total: int,
    limit: int,
    result: int,
)
    requires
        0 <= component_start <= index <= end <= input.len(),
        component_start < end,
        -1 <= previous_rank <= 4,
        0 <= total <= limit,
        limit == 9_223_372_036_854_775_807
            || limit == 9_223_372_036_854_775_808,
        forall|position: int| component_start <= position < end ==>
            #[trigger] triptych_is_digit(input[position]),
        triptych_nat_of(input.subrange(component_start, end))
            <= 9_223_372_036_854_775_808,
        duration_parse_state(
            input,
            end,
            previous_rank,
            total,
            limit,
            triptych_nat_of(input.subrange(component_start, end)),
            true,
        ) == Some(result),
    ensures
        duration_parse_state(
            input,
            index,
            previous_rank,
            total,
            limit,
            triptych_nat_of(input.subrange(component_start, index)),
            component_start < index,
        ) == Some(result),
    decreases end - index,
{
    if index < end {
        let digits = input.subrange(component_start, index);
        let next_digits = input.subrange(component_start, index + 1);
        assert(next_digits == digits.push(input[index])) by {
            assert_seqs_equal!(next_digits == digits.push(input[index]));
        }
        assert(triptych_is_digit(input[index]));
        duration_triptych_nat_of_push_digit(digits, input[index]);
        assert(duration_is_digit(input[index])) by {
            reveal(duration_is_digit);
            reveal(triptych_is_digit);
        }
        assert(duration_digit_value(input[index])
            == input[index] as int - TRIPTYCH_ZERO as int) by {
            reveal(duration_digit_value);
        }
        duration_nat_of_subrange_prefix_le(
            input,
            component_start,
            index + 1,
            end,
        );
        duration_parse_state_complete_digits(
            input,
            component_start,
            index + 1,
            end,
            previous_rank,
            total,
            limit,
            result,
        );
        reveal(duration_parse_state);
    }
}

pub open spec fn duration_unit_text(rank: int) -> Seq<char> {
    if rank == 0 {
        seq!['d']
    } else if rank == 1 {
        seq!['h']
    } else if rank == 2 {
        seq!['m']
    } else if rank == 3 {
        seq!['s']
    } else {
        seq!['m', 's']
    }
}

pub proof fn duration_parse_component_complete(
    input: Seq<char>,
    start: int,
    digits: Seq<char>,
    previous_rank: int,
    rank: int,
    total: int,
    limit: int,
    result: int,
)
    requires
        0 <= start,
        1 <= digits.len(),
        start + digits.len() + duration_unit_text(rank).len() <= input.len(),
        input.subrange(start, start + digits.len()) == digits,
        input.subrange(
            start + digits.len(),
            start + digits.len() + duration_unit_text(rank).len(),
        ) == duration_unit_text(rank),
        forall|position: int| 0 <= position < digits.len() ==>
            #[trigger] triptych_is_digit(digits[position]),
        -1 <= previous_rank < rank <= 4,
        0 <= total <= limit,
        limit == 9_223_372_036_854_775_807
            || limit == 9_223_372_036_854_775_808,
        triptych_nat_of(digits) <= 9_223_372_036_854_775_808,
        triptych_nat_of(digits) * duration_unit_multiplier(rank)
            <= limit - total,
        rank != 2
            || start + digits.len() + 1 == input.len()
            || duration_is_digit(input[start + digits.len() + 1]),
        duration_parse_state(
            input,
            start + digits.len() + duration_unit_text(rank).len(),
            rank,
            total + triptych_nat_of(digits) * duration_unit_multiplier(rank),
            limit,
            0,
            false,
        ) == Some(result),
    ensures
        duration_parse_state(
            input,
            start,
            previous_rank,
            total,
            limit,
            0,
            false,
        ) == Some(result),
{
    let end = start + digits.len();
    let next = end + duration_unit_text(rank).len();
    assert forall|position: int| start <= position < end implies
        #[trigger] triptych_is_digit(input[position]) by {
        assert(input[position] == digits[position - start]);
    }
    duration_nat_of_subrange_nonnegative(input, start, end);
    assert(0 <= triptych_nat_of(digits));
    assert(duration_parse_state(
        input,
        end,
        previous_rank,
        total,
        limit,
        triptych_nat_of(digits),
        true,
    ) == Some(result)) by {
        reveal(duration_unit_text);
        if rank == 0 {
            assert(input.subrange(end, end + 1) == seq!['d']);
            assert(input.subrange(end, end + 1)[0] == input[end]);
            assert(input[end] == 'd');
            assert(next == end + 1);
        } else if rank == 1 {
            assert(input.subrange(end, end + 1) == seq!['h']);
            assert(input.subrange(end, end + 1)[0] == input[end]);
            assert(input[end] == 'h');
            assert(next == end + 1);
        } else if rank == 2 {
            assert(input.subrange(end, end + 1) == seq!['m']);
            assert(input.subrange(end, end + 1)[0] == input[end]);
            assert(input[end] == 'm');
            assert(next == end + 1);
            if next < input.len() {
                assert(duration_is_digit(input[next]));
                assert(input[next] != 's') by {
                    reveal(duration_is_digit);
                }
            }
        } else if rank == 3 {
            assert(input.subrange(end, end + 1) == seq!['s']);
            assert(input.subrange(end, end + 1)[0] == input[end]);
            assert(input[end] == 's');
            assert(next == end + 1);
        } else {
            assert(rank == 4);
            assert(input.subrange(end, end + 2) == seq!['m', 's']);
            assert(input.subrange(end, end + 2)[0] == input[end]);
            assert(input.subrange(end, end + 2)[1] == input[end + 1]);
            assert(input[end] == 'm');
            assert(input[end + 1] == 's');
            assert(next == end + 2);
        }
        reveal(duration_parse_state);
        reveal(duration_is_digit);
        reveal(triptych_is_digit);
        reveal(duration_unit_rank);
        reveal(duration_unit_length);
        reveal(duration_unit_multiplier);
    }
    duration_parse_state_complete_digits(
        input,
        start,
        start,
        end,
        previous_rank,
        total,
        limit,
        result,
    );
    assert(input.subrange(start, start) == Seq::<char>::empty());
    assert(triptych_nat_of(input.subrange(start, start)) == 0) by {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
}

pub proof fn duration_digits_nat_nonnegative(digits: Seq<char>)
    requires
        duration_digits_wf(digits),
    ensures
        0 <= triptych_nat_of(digits),
{
    reveal(duration_digits_wf);
    if digits.len() == 0 {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    } else {
        duration_nat_of_subrange_nonnegative(
            digits,
            0,
            digits.len() as int,
        );
        assert(digits.subrange(0, digits.len() as int) == digits) by {
            assert_seqs_equal!(
                digits.subrange(0, digits.len() as int) == digits
            );
        }
    }
}

pub proof fn duration_parts_value_nonnegative(parts: DurationParts)
    requires
        duration_parts_after(parts, -1),
    ensures
        0 <= duration_parts_value(parts),
{
    reveal(duration_parts_after);
    duration_digits_nat_nonnegative(parts.d_days);
    duration_digits_nat_nonnegative(parts.d_hours);
    duration_digits_nat_nonnegative(parts.d_minutes);
    duration_digits_nat_nonnegative(parts.d_seconds);
    duration_digits_nat_nonnegative(parts.d_millis);
    reveal(duration_parts_value);
}

pub proof fn duration_parts_text_starts_digit(
    parts: DurationParts,
    previous_rank: int,
)
    requires
        duration_parts_after(parts, previous_rank),
        -1 <= previous_rank < 4,
        0 < duration_parts_text(parts).len(),
    ensures
        triptych_is_digit(duration_parts_text(parts)[0]),
        duration_is_digit(duration_parts_text(parts)[0]),
{
    reveal(duration_parts_after);
    reveal(duration_digits_wf);
    reveal(duration_parts_text);
    reveal(duration_part_text);
    if parts.d_days.len() != 0 {
        assert(previous_rank < 0);
        assert(duration_parts_text(parts)[0] == parts.d_days[0]);
        assert(triptych_is_digit(parts.d_days[0]));
    } else if parts.d_hours.len() != 0 {
        if previous_rank >= 1 {
            assert(false);
        }
        assert(duration_parts_text(parts)[0] == parts.d_hours[0]);
        assert(triptych_is_digit(parts.d_hours[0]));
    } else if parts.d_minutes.len() != 0 {
        if previous_rank >= 2 {
            assert(false);
        }
        assert(duration_parts_text(parts)[0] == parts.d_minutes[0]);
        assert(triptych_is_digit(parts.d_minutes[0]));
    } else if parts.d_seconds.len() != 0 {
        if previous_rank >= 3 {
            assert(false);
        }
        assert(duration_parts_text(parts)[0] == parts.d_seconds[0]);
        assert(triptych_is_digit(parts.d_seconds[0]));
    } else {
        assert(parts.d_millis.len() != 0);
        assert(duration_parts_text(parts)[0] == parts.d_millis[0]);
        assert(triptych_is_digit(parts.d_millis[0]));
    }
    reveal(duration_is_digit);
    reveal(triptych_is_digit);
}

pub proof fn duration_digits_ascii(digits: Seq<char>)
    requires
        duration_digits_wf(digits),
    ensures
        is_ascii_chars(digits),
{
    reveal(duration_digits_wf);
    reveal(is_ascii_chars);
    assert forall|index: int| 0 <= index < digits.len() implies
        '\0' <= #[trigger] digits[index] <= '\u{7f}' by {
        assert(triptych_is_digit(digits[index]));
        reveal(triptych_is_digit);
    }
}

pub proof fn duration_part_text_ascii(digits: Seq<char>, rank: int)
    requires
        duration_digits_wf(digits),
        0 <= rank <= 4,
    ensures
        is_ascii_chars(duration_part_text(digits, rank)),
{
    duration_digits_ascii(digits);
    reveal(duration_part_text);
    reveal(is_ascii_chars);
    if digits.len() != 0 {
        assert forall|index: int|
            0 <= index < duration_part_text(digits, rank).len() implies
                '\0' <= #[trigger] duration_part_text(digits, rank)[index]
                    <= '\u{7f}' by {
            if index < digits.len() {
                assert(duration_part_text(digits, rank)[index] == digits[index]);
            } else {
                if rank == 4 {
                    assert(index == digits.len() || index == digits.len() + 1);
                } else {
                    assert(index == digits.len());
                }
            }
        }
    }
}

pub proof fn duration_parts_text_ascii(parts: DurationParts)
    requires
        duration_parts_after(parts, -1),
    ensures
        is_ascii_chars(duration_parts_text(parts)),
{
    reveal(duration_parts_after);
    duration_part_text_ascii(parts.d_days, 0);
    duration_part_text_ascii(parts.d_hours, 1);
    duration_part_text_ascii(parts.d_minutes, 2);
    duration_part_text_ascii(parts.d_seconds, 3);
    duration_part_text_ascii(parts.d_millis, 4);
    let days = duration_part_text(parts.d_days, 0);
    let hours = duration_part_text(parts.d_hours, 1);
    let minutes = duration_part_text(parts.d_minutes, 2);
    let seconds = duration_part_text(parts.d_seconds, 3);
    let millis = duration_part_text(parts.d_millis, 4);
    let first = days + hours;
    let second = first + minutes;
    let third = second + seconds;
    let all = third + millis;
    vstd::utf8::is_ascii_chars_concat(first, days, hours);
    vstd::utf8::is_ascii_chars_concat(second, first, minutes);
    vstd::utf8::is_ascii_chars_concat(third, second, seconds);
    vstd::utf8::is_ascii_chars_concat(all, third, millis);
    reveal(duration_parts_text);
}

pub open spec fn duration_parts_first_rank(parts: DurationParts) -> int {
    if parts.d_days.len() != 0 {
        0
    } else if parts.d_hours.len() != 0 {
        1
    } else if parts.d_minutes.len() != 0 {
        2
    } else if parts.d_seconds.len() != 0 {
        3
    } else {
        4
    }
}

pub open spec fn duration_parts_first_digits(parts: DurationParts) -> Seq<char> {
    if parts.d_days.len() != 0 {
        parts.d_days
    } else if parts.d_hours.len() != 0 {
        parts.d_hours
    } else if parts.d_minutes.len() != 0 {
        parts.d_minutes
    } else if parts.d_seconds.len() != 0 {
        parts.d_seconds
    } else {
        parts.d_millis
    }
}

pub open spec fn duration_parts_tail(parts: DurationParts) -> DurationParts {
    if parts.d_days.len() != 0 {
        DurationParts {
            d_days: Seq::<char>::empty(),
            d_hours: parts.d_hours,
            d_minutes: parts.d_minutes,
            d_seconds: parts.d_seconds,
            d_millis: parts.d_millis,
        }
    } else if parts.d_hours.len() != 0 {
        DurationParts {
            d_days: parts.d_days,
            d_hours: Seq::<char>::empty(),
            d_minutes: parts.d_minutes,
            d_seconds: parts.d_seconds,
            d_millis: parts.d_millis,
        }
    } else if parts.d_minutes.len() != 0 {
        DurationParts {
            d_days: parts.d_days,
            d_hours: parts.d_hours,
            d_minutes: Seq::<char>::empty(),
            d_seconds: parts.d_seconds,
            d_millis: parts.d_millis,
        }
    } else if parts.d_seconds.len() != 0 {
        DurationParts {
            d_days: parts.d_days,
            d_hours: parts.d_hours,
            d_minutes: parts.d_minutes,
            d_seconds: Seq::<char>::empty(),
            d_millis: parts.d_millis,
        }
    } else {
        DurationParts {
            d_days: parts.d_days,
            d_hours: parts.d_hours,
            d_minutes: parts.d_minutes,
            d_seconds: parts.d_seconds,
            d_millis: Seq::<char>::empty(),
        }
    }
}

pub proof fn duration_parts_head_facts(
    parts: DurationParts,
    previous_rank: int,
)
    requires
        -1 <= previous_rank < 4,
        duration_parts_after(parts, previous_rank),
        0 < duration_parts_text(parts).len(),
    ensures
        ({
            let rank = duration_parts_first_rank(parts);
            let digits = duration_parts_first_digits(parts);
            let tail = duration_parts_tail(parts);
            &&& previous_rank < rank <= 4
            &&& 1 <= digits.len()
            &&& (forall|position: int| 0 <= position < digits.len() ==>
                #[trigger] triptych_is_digit(digits[position]))
            &&& duration_parts_text(parts)
                == digits + duration_unit_text(rank) + duration_parts_text(tail)
            &&& duration_parts_after(tail, rank)
            &&& duration_parts_value(parts)
                == triptych_nat_of(digits) * duration_unit_multiplier(rank)
                    + duration_parts_value(tail)
        }),
{
    reveal(duration_parts_after);
    reveal(duration_digits_wf);
    reveal(duration_parts_first_rank);
    reveal(duration_parts_first_digits);
    reveal(duration_parts_tail);
    reveal(duration_parts_text);
    reveal(duration_part_text);
    reveal(duration_unit_text);
    reveal(duration_parts_value);
    reveal(duration_unit_multiplier);
    if parts.d_days.len() != 0 {
        assert(previous_rank < 0);
    } else if parts.d_hours.len() != 0 {
        assert(previous_rank < 1);
    } else if parts.d_minutes.len() != 0 {
        assert(previous_rank < 2);
    } else if parts.d_seconds.len() != 0 {
        assert(previous_rank < 3);
    } else {
        assert(parts.d_millis.len() != 0);
        assert(previous_rank < 4);
    }
}

pub proof fn duration_parts_text_nonempty_length(parts: DurationParts)
    requires
        duration_parts_after(parts, -1),
        0 < duration_parts_text(parts).len(),
    ensures
        2 <= duration_parts_text(parts).len(),
{
    duration_parts_head_facts(parts, -1);
    let rank = duration_parts_first_rank(parts);
    let digits = duration_parts_first_digits(parts);
    let tail = duration_parts_tail(parts);
    reveal(duration_unit_text);
    assert(1 <= duration_unit_text(rank).len());
    assert(
        duration_parts_text(parts)
            == digits + duration_unit_text(rank) + duration_parts_text(tail)
    );
}

#[verifier::rlimit(100)]
pub proof fn duration_parse_state_complete_parts(
    input: Seq<char>,
    index: int,
    previous_rank: int,
    total: int,
    limit: int,
    parts: DurationParts,
)
    requires
        0 <= index <= input.len(),
        -1 <= previous_rank <= 4,
        0 <= total <= limit,
        limit == 9_223_372_036_854_775_807
            || limit == 9_223_372_036_854_775_808,
        input.subrange(index, input.len() as int) == duration_parts_text(parts),
        duration_parts_after(parts, previous_rank),
        total + duration_parts_value(parts) <= limit,
        previous_rank < 0 ==> 0 < duration_parts_text(parts).len(),
    ensures
        duration_parse_state(
            input,
            index,
            previous_rank,
            total,
            limit,
            0,
            false,
        ) == Some(total + duration_parts_value(parts)),
    decreases 5 - previous_rank,
{
    duration_parts_value_nonnegative(parts);
    if duration_parts_text(parts).len() == 0 {
        assert(0 <= previous_rank);
        assert(index == input.len());
        assert(duration_parts_value(parts) == 0) by {
            reveal(duration_parts_text);
            reveal(duration_part_text);
            reveal(duration_parts_after);
            reveal(duration_parts_value);
            reveal(triptych_nat_of);
            reveal_with_fuel(triptych_nat_of_from, 2);
        }
        reveal(duration_parse_state);
    } else {
        assert(previous_rank < 4);
        duration_parts_head_facts(parts, previous_rank);
        let rank = duration_parts_first_rank(parts);
        let digits = duration_parts_first_digits(parts);
        let tail = duration_parts_tail(parts);
        let suffix = input.subrange(index, input.len() as int);
        let unit = duration_unit_text(rank);
        let tail_text = duration_parts_text(tail);
        let end = index + digits.len();
        let next = end + unit.len();
        assert(0 <= rank <= 4);
        assert(index < end <= next <= input.len());
        assert(suffix == digits + unit + tail_text);
        assert(input.subrange(index, end) == digits) by {
            assert_seqs_equal!(input.subrange(index, end) == digits);
        }
        assert(input.subrange(end, next) == unit) by {
            assert_seqs_equal!(input.subrange(end, next) == unit, position => {
                assert(input.subrange(end, next)[position]
                    == input[end + position]);
                assert(suffix[digits.len() + position]
                    == input[end + position]);
                assert((digits + unit + tail_text)[digits.len() + position]
                    == unit[position]);
            });
        }
        assert(input.subrange(next, input.len() as int) == tail_text) by {
            assert_seqs_equal!(
                input.subrange(next, input.len() as int) == tail_text,
                position => {
                    assert(input.subrange(next, input.len() as int)[position]
                        == input[next + position]);
                    assert(suffix[digits.len() + unit.len() + position]
                        == input[next + position]);
                    assert((digits + unit + tail_text)[
                        digits.len() + unit.len() + position
                    ] == tail_text[position]);
                }
            );
        }
        assert(duration_parts_after(tail, -1)) by {
            reveal(duration_parts_after);
        }
        duration_parts_value_nonnegative(tail);
        duration_digits_nat_nonnegative(digits);
        let contribution =
            triptych_nat_of(digits) * duration_unit_multiplier(rank);
        assert(0 <= contribution);
        assert(total + contribution + duration_parts_value(tail) <= limit);
        assert(contribution <= limit - total);
        reveal(duration_unit_multiplier);
        assert(triptych_nat_of(digits) <= 9_223_372_036_854_775_808);
        if rank == 2 && next < input.len() {
            assert(0 < duration_parts_text(tail).len());
            duration_parts_text_starts_digit(tail, rank);
            assert(input[next] == duration_parts_text(tail)[0]);
            assert(duration_is_digit(input[next]));
        }
        duration_parse_state_complete_parts(
            input,
            next,
            rank,
            total + contribution,
            limit,
            tail,
        );
        duration_parse_component_complete(
            input,
            index,
            digits,
            previous_rank,
            rank,
            total,
            limit,
            total + duration_parts_value(parts),
        );
    }
}

pub open spec fn duration_view_parts(view: DurationView) -> DurationParts {
    DurationParts {
        d_days: view.d_days,
        d_hours: view.d_hours,
        d_minutes: view.d_minutes,
        d_seconds: view.d_seconds,
        d_millis: view.d_millis,
    }
}

pub proof fn duration_matches_view_parts(input: Seq<char>, view: DurationView)
    requires
        duration_matches_view(input, view),
    ensures
        ({
            let parts = duration_view_parts(view);
            &&& input == view.sign + duration_parts_text(parts)
            &&& (view.sign.len() == 0 || view.sign == seq!['-'])
            &&& view.components == duration_parts_text(parts)
            &&& duration_parts_after(parts, -1)
        }),
{
    reveal(duration_matches_view);
    reveal(duration_matches_Duration);
    let sign = choose|sign: Seq<char>|
        exists|components: Seq<char>|
            input == sign + components
                && (view.sign == sign
                    && #[trigger] duration_matches_Sign(sign, view))
                && (view.components == components
                    && duration_matches_Components(components, view));
    let components = choose|components: Seq<char>|
        input == sign + components
            && (view.sign == sign && duration_matches_Sign(sign, view))
            && (view.components == components
                && #[trigger] duration_matches_Components(components, view));
    reveal(duration_matches_Sign);
    assert(view.sign.len() == 0 || view.sign == seq!['-']);
    assert(duration_matches_Components(components, view));
    reveal(duration_matches_Components);
    assert(exists|days: Seq<char>, hours: Seq<char>, minutes: Seq<char>,
            seconds: Seq<char>, millis: Seq<char>|
        components == days + hours + minutes + seconds + millis
            && (days.len() == 0 && view.d_days == seq![]
                || duration_matches_Days(days, view))
            && (hours.len() == 0 && view.d_hours == seq![]
                || duration_matches_Hours(hours, view))
            && (minutes.len() == 0 && view.d_minutes == seq![]
                || duration_matches_Minutes(minutes, view))
            && (seconds.len() == 0 && view.d_seconds == seq![]
                || duration_matches_Seconds(seconds, view))
            && (millis.len() == 0 && view.d_millis == seq![]
                || duration_matches_Millis(millis, view))) by {
    }
    let (days, hours, minutes, seconds, millis): (
        Seq<char>,
        Seq<char>,
        Seq<char>,
        Seq<char>,
        Seq<char>,
    ) = choose|days: Seq<char>, hours: Seq<char>, minutes: Seq<char>,
                    seconds: Seq<char>, millis: Seq<char>|
        components == days + hours + minutes + seconds + millis
            && (days.len() == 0 && view.d_days == seq![]
                || duration_matches_Days(days, view))
            && (hours.len() == 0 && view.d_hours == seq![]
                || duration_matches_Hours(hours, view))
            && (minutes.len() == 0 && view.d_minutes == seq![]
                || duration_matches_Minutes(minutes, view))
            && (seconds.len() == 0 && view.d_seconds == seq![]
                || duration_matches_Seconds(seconds, view))
            && (millis.len() == 0 && view.d_millis == seq![]
                || duration_matches_Millis(millis, view));
    if days.len() == 0 {
        assert(view.d_days == seq![]);
        assert(days == duration_part_text(view.d_days, 0)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_days)) by {
            reveal(duration_digits_wf);
        }
    } else {
        reveal(duration_matches_Days);
        let digits = choose|digits: Seq<char>|
            days == digits + seq!['d']
                && view.d_days == digits
                && #[trigger] duration_matches_DDays(digits, view);
        reveal(duration_matches_DDays);
        assert(days == duration_part_text(view.d_days, 0)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_days)) by {
            reveal(duration_digits_wf);
        }
    }
    if hours.len() == 0 {
        assert(view.d_hours == seq![]);
        assert(hours == duration_part_text(view.d_hours, 1)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_hours)) by {
            reveal(duration_digits_wf);
        }
    } else {
        reveal(duration_matches_Hours);
        let digits = choose|digits: Seq<char>|
            hours == digits + seq!['h']
                && view.d_hours == digits
                && #[trigger] duration_matches_DHours(digits, view);
        reveal(duration_matches_DHours);
        assert(hours == duration_part_text(view.d_hours, 1)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_hours)) by {
            reveal(duration_digits_wf);
        }
    }
    if minutes.len() == 0 {
        assert(view.d_minutes == seq![]);
        assert(minutes == duration_part_text(view.d_minutes, 2)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_minutes)) by {
            reveal(duration_digits_wf);
        }
    } else {
        reveal(duration_matches_Minutes);
        let digits = choose|digits: Seq<char>|
            minutes == digits + seq!['m']
                && view.d_minutes == digits
                && #[trigger] duration_matches_DMinutes(digits, view);
        reveal(duration_matches_DMinutes);
        assert(minutes == duration_part_text(view.d_minutes, 2)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_minutes)) by {
            reveal(duration_digits_wf);
        }
    }
    if seconds.len() == 0 {
        assert(view.d_seconds == seq![]);
        assert(seconds == duration_part_text(view.d_seconds, 3)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_seconds)) by {
            reveal(duration_digits_wf);
        }
    } else {
        reveal(duration_matches_Seconds);
        let digits = choose|digits: Seq<char>|
            seconds == digits + seq!['s']
                && view.d_seconds == digits
                && #[trigger] duration_matches_DSeconds(digits, view);
        reveal(duration_matches_DSeconds);
        assert(seconds == duration_part_text(view.d_seconds, 3)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_seconds)) by {
            reveal(duration_digits_wf);
        }
    }
    if millis.len() == 0 {
        assert(view.d_millis == seq![]);
        assert(millis == duration_part_text(view.d_millis, 4)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_millis)) by {
            reveal(duration_digits_wf);
        }
    } else {
        reveal(duration_matches_Millis);
        let digits = choose|digits: Seq<char>|
            millis == digits + seq!['m', 's']
                && view.d_millis == digits
                && #[trigger] duration_matches_DMillis(digits, view);
        reveal(duration_matches_DMillis);
        assert(millis == duration_part_text(view.d_millis, 4)) by {
            reveal(duration_part_text);
        }
        assert(duration_digits_wf(view.d_millis)) by {
            reveal(duration_digits_wf);
        }
    }
    let parts = duration_view_parts(view);
    assert(components == duration_parts_text(parts)) by {
        reveal(duration_view_parts);
        reveal(duration_parts_text);
    }
    assert(duration_parts_after(parts, -1)) by {
        reveal(duration_view_parts);
        reveal(duration_parts_after);
    }
    reveal(duration_view_parts);
}

pub proof fn duration_generated_view_parses(
    input: Seq<char>,
    view: DurationView,
)
    requires
        duration_matches_view(input, view),
        duration_view_valid(view),
    ensures
        duration_parse_spec(input) == Some(duration_view_denotation(view)),
{
    duration_matches_view_parts(input, view);
    let parts = duration_view_parts(view);
    let components = duration_parts_text(parts);
    reveal(duration_view_valid);
    reveal(duration_view_wf_constraints);
    reveal(duration_wf_constraints);
    assert(0 < components.len());
    duration_parts_text_ascii(parts);
    let negative = view.sign == seq!['-'];
    let start: int = if negative { 1 } else { 0 };
    if negative {
        assert(view.sign.len() == 1);
        assert(input[0] == '-');
    } else {
        assert(view.sign.len() == 0);
        duration_parts_text_starts_digit(parts, -1);
        assert(input == components);
        assert(input[0] == components[0]);
        assert(triptych_is_digit(input[0]));
        assert(input[0] != '-') by {
            reveal(triptych_is_digit);
        }
    }
    assert(start < input.len());
    assert(input.subrange(start, input.len() as int) == components) by {
        assert_seqs_equal!(
            input.subrange(start, input.len() as int) == components
        );
    }
    assert(is_ascii_chars(view.sign)) by {
        reveal(is_ascii_chars);
        if view.sign.len() != 0 {
            assert(view.sign == seq!['-']);
        }
    }
    assert(is_ascii_chars(input)) by {
        vstd::utf8::is_ascii_chars_concat(input, view.sign, components);
    }
    let magnitude = duration_parts_value(parts);
    duration_parts_value_nonnegative(parts);
    assert(duration_view_denotation(view)
        == triptych_sign_of(view.sign) * magnitude) by {
        reveal(duration_view_denotation);
        reveal(duration_value);
        reveal(duration_view_parts);
        reveal(duration_parts_value);
    }
    reveal(duration_view_constraints);
    reveal(duration_constraints);
    let limit: int = if negative {
        9_223_372_036_854_775_808
    } else {
        9_223_372_036_854_775_807
    };
    if negative {
        assert(triptych_sign_of(view.sign) == -1) by {
            reveal(triptych_sign_of);
        }
        assert(magnitude <= limit);
    } else {
        assert(triptych_sign_of(view.sign) == 1) by {
            reveal(triptych_sign_of);
        }
        assert(magnitude <= limit);
    }
    duration_parse_state_complete_parts(
        input,
        start,
        -1,
        0,
        limit,
        parts,
    );
    reveal(duration_parse_spec);
}

pub proof fn duration_valid_has_result(input: Seq<char>)
    requires
        duration_is_valid(input),
    ensures
        exists|value: int| duration_matches_result(input, value),
{
    reveal(duration_is_valid);
    reveal(duration_is_wf);
    reveal(duration_satisfies_wf_constraints);
    let wf_view = choose|view: DurationView|
        duration_matches_view(input, view)
            && duration_view_wf_constraints(view);
    duration_matches_view_parts(input, wf_view);
    let wf_parts = duration_view_parts(wf_view);
    reveal(duration_view_wf_constraints);
    reveal(duration_wf_constraints);
    assert(0 < duration_parts_text(wf_parts).len());
    duration_parts_text_nonempty_length(wf_parts);
    assert(2 <= input.len());

    reveal(duration_satisfies_constraints);
    let bounded_view = choose|view: DurationView|
        duration_matches_view(input, view)
            && duration_view_constraints(view);
    duration_matches_view_parts(input, bounded_view);
    let bounded_parts = duration_view_parts(bounded_view);
    if duration_parts_text(bounded_parts).len() == 0 {
        assert(input.len() <= 1);
        assert(false);
    }
    assert(duration_view_wf_constraints(bounded_view)) by {
        reveal(duration_view_wf_constraints);
        reveal(duration_wf_constraints);
    }
    assert(duration_view_valid(bounded_view)) by {
        reveal(duration_view_valid);
    }
    let value = duration_view_denotation(bounded_view);
    assert(duration_matches_result(input, value)) by {
        reveal(duration_matches_result);
        assert(exists|view: DurationView|
            duration_matches_view(input, view)
                && duration_view_valid(view)
                && duration_view_denotation(view) == value) by {
            assert(
                duration_matches_view(input, bounded_view)
                    && duration_view_valid(bounded_view)
                    && duration_view_denotation(bounded_view) == value
            );
        }
    }
    assert(exists|candidate: int| duration_matches_result(input, candidate)) by {
        assert(duration_matches_result(input, value));
    }
}

#[verifier::rlimit(100)]
pub proof fn duration_parse_state_sound_parts(
    input: Seq<char>,
    component_start: int,
    index: int,
    previous_rank: int,
    total: int,
    limit: int,
    quantity: int,
    in_digits: bool,
    result: int,
)
    requires
        0 <= component_start <= index <= input.len(),
        -1 <= previous_rank <= 4,
        0 <= total <= limit,
        limit == 9_223_372_036_854_775_807
            || limit == 9_223_372_036_854_775_808,
        in_digits == (component_start < index),
        quantity == triptych_nat_of(input.subrange(component_start, index)),
        quantity <= 9_223_372_036_854_775_808,
        forall|position: int| component_start <= position < index ==>
            #[trigger] triptych_is_digit(input[position]),
        duration_parse_state(
            input,
            index,
            previous_rank,
            total,
            limit,
            quantity,
            in_digits,
        ) == Some(result),
    ensures
        exists|parts: DurationParts|
            input.subrange(component_start, input.len() as int)
                == duration_parts_text(parts)
                && duration_parts_after(parts, previous_rank)
                && result == total + duration_parts_value(parts),
        total <= result <= limit,
    decreases input.len() - index,
{
    reveal(duration_parse_state);
    if index == input.len() {
        let empty = Seq::<char>::empty();
        let parts = DurationParts {
            d_days: empty,
            d_hours: empty,
            d_minutes: empty,
            d_seconds: empty,
            d_millis: empty,
        };
        assert(component_start == index);
        assert(input.subrange(component_start, input.len() as int) == empty);
        assert(duration_parts_text(parts) == empty) by {
            reveal(duration_parts_text);
            reveal(duration_part_text);
        }
        assert(duration_parts_after(parts, previous_rank)) by {
            reveal(duration_parts_after);
            reveal(duration_digits_wf);
        }
        assert(duration_parts_value(parts) == 0) by {
            reveal(duration_parts_value);
            reveal(triptych_nat_of);
            reveal_with_fuel(triptych_nat_of_from, 2);
        }
        assert(exists|candidate: DurationParts|
            input.subrange(component_start, input.len() as int)
                    == duration_parts_text(candidate)
                && duration_parts_after(candidate, previous_rank)
                && result == total + duration_parts_value(candidate)) by {
            assert(
                input.subrange(component_start, input.len() as int)
                        == duration_parts_text(parts)
                    && duration_parts_after(parts, previous_rank)
                    && result == total + duration_parts_value(parts)
            );
        }
    } else if duration_is_digit(input[index]) {
        let digits = input.subrange(component_start, index);
        let next_digits = input.subrange(component_start, index + 1);
        let next_quantity =
            quantity * 10 + duration_digit_value(input[index]);
        assert(triptych_is_digit(input[index])) by {
            reveal(duration_is_digit);
            reveal(triptych_is_digit);
        }
        assert(next_digits == digits.push(input[index])) by {
            assert_seqs_equal!(next_digits == digits.push(input[index]));
        }
        duration_triptych_nat_of_push_digit(digits, input[index]);
        assert(duration_digit_value(input[index])
            == input[index] as int - TRIPTYCH_ZERO as int) by {
            reveal(duration_digit_value);
        }
        assert(next_quantity == triptych_nat_of(next_digits));
        assert forall|position: int| component_start <= position < index + 1 implies
            #[trigger] triptych_is_digit(input[position]) by {
            if position < index {
            } else {
                assert(position == index);
            }
        }
        if next_quantity > 9_223_372_036_854_775_808 {
            assert(false);
        } else {
            duration_parse_state_sound_parts(
                input,
                component_start,
                index + 1,
                previous_rank,
                total,
                limit,
                next_quantity,
                true,
                result,
            );
        }
    } else if !in_digits {
        assert(false);
    } else {
        let rank = duration_unit_rank(input, index);
        let unit_length = duration_unit_length(input, index);
        let next = index + unit_length;
        let contribution = quantity * duration_unit_multiplier(rank);
        if rank < 0
            || rank <= previous_rank
            || next > input.len()
            || contribution > limit - total
        {
            assert(false);
        } else {
            assert(0 <= rank <= 4);
            duration_parse_state_sound_parts(
                input,
                next,
                next,
                rank,
                total + contribution,
                limit,
                0,
                false,
                result,
            );
            let tail = choose|parts: DurationParts|
                input.subrange(next, input.len() as int) == duration_parts_text(parts)
                    && duration_parts_after(parts, rank)
                    && result == total + contribution + duration_parts_value(parts);
            let digits = input.subrange(component_start, index);
            assert(1 <= digits.len());
            assert forall|position: int| 0 <= position < digits.len() implies
                #[trigger] triptych_is_digit(digits[position]) by {
                assert(digits[position] == input[component_start + position]);
            }
            let parts = if rank == 0 {
                DurationParts {
                    d_days: digits,
                    d_hours: tail.d_hours,
                    d_minutes: tail.d_minutes,
                    d_seconds: tail.d_seconds,
                    d_millis: tail.d_millis,
                }
            } else if rank == 1 {
                DurationParts {
                    d_days: tail.d_days,
                    d_hours: digits,
                    d_minutes: tail.d_minutes,
                    d_seconds: tail.d_seconds,
                    d_millis: tail.d_millis,
                }
            } else if rank == 2 {
                DurationParts {
                    d_days: tail.d_days,
                    d_hours: tail.d_hours,
                    d_minutes: digits,
                    d_seconds: tail.d_seconds,
                    d_millis: tail.d_millis,
                }
            } else if rank == 3 {
                DurationParts {
                    d_days: tail.d_days,
                    d_hours: tail.d_hours,
                    d_minutes: tail.d_minutes,
                    d_seconds: digits,
                    d_millis: tail.d_millis,
                }
            } else {
                DurationParts {
                    d_days: tail.d_days,
                    d_hours: tail.d_hours,
                    d_minutes: tail.d_minutes,
                    d_seconds: tail.d_seconds,
                    d_millis: digits,
                }
            };
            reveal(duration_unit_rank);
            reveal(duration_unit_length);
            reveal(duration_unit_multiplier);
            if rank == 0 {
                assert(input[index] == 'd');
                assert(next == index + 1);
                assert(tail.d_days.len() == 0) by {
                    reveal(duration_parts_after);
                }
                assert(input.subrange(component_start, input.len() as int)
                    == digits + seq!['d'] + input.subrange(next, input.len() as int)) by {
                    assert_seqs_equal!(
                        input.subrange(component_start, input.len() as int)
                            == digits + seq!['d'] + input.subrange(next, input.len() as int)
                    );
                }
                reveal(duration_parts_text);
                reveal(duration_part_text);
                assert_seqs_equal!(
                    input.subrange(component_start, input.len() as int)
                        == duration_parts_text(parts)
                );
            } else if rank == 1 {
                assert(input[index] == 'h');
                assert(next == index + 1);
                assert(tail.d_days.len() == 0 && tail.d_hours.len() == 0) by {
                    reveal(duration_parts_after);
                }
                assert(input.subrange(component_start, input.len() as int)
                    == digits + seq!['h'] + input.subrange(next, input.len() as int)) by {
                    assert_seqs_equal!(
                        input.subrange(component_start, input.len() as int)
                            == digits + seq!['h'] + input.subrange(next, input.len() as int)
                    );
                }
                reveal(duration_parts_text);
                reveal(duration_part_text);
                assert_seqs_equal!(
                    input.subrange(component_start, input.len() as int)
                        == duration_parts_text(parts)
                );
            } else if rank == 2 {
                assert(input[index] == 'm');
                assert(next == index + 1);
                assert(
                    tail.d_days.len() == 0
                        && tail.d_hours.len() == 0
                        && tail.d_minutes.len() == 0
                ) by {
                    reveal(duration_parts_after);
                }
                assert(input.subrange(component_start, input.len() as int)
                    == digits + seq!['m'] + input.subrange(next, input.len() as int)) by {
                    assert_seqs_equal!(
                        input.subrange(component_start, input.len() as int)
                            == digits + seq!['m'] + input.subrange(next, input.len() as int)
                    );
                }
                reveal(duration_parts_text);
                reveal(duration_part_text);
                assert_seqs_equal!(
                    input.subrange(component_start, input.len() as int)
                        == duration_parts_text(parts)
                );
            } else if rank == 3 {
                assert(input[index] == 's');
                assert(next == index + 1);
                assert(
                    tail.d_days.len() == 0
                        && tail.d_hours.len() == 0
                        && tail.d_minutes.len() == 0
                        && tail.d_seconds.len() == 0
                ) by {
                    reveal(duration_parts_after);
                }
                assert(input.subrange(component_start, input.len() as int)
                    == digits + seq!['s'] + input.subrange(next, input.len() as int)) by {
                    assert_seqs_equal!(
                        input.subrange(component_start, input.len() as int)
                            == digits + seq!['s'] + input.subrange(next, input.len() as int)
                    );
                }
                reveal(duration_parts_text);
                reveal(duration_part_text);
                assert_seqs_equal!(
                    input.subrange(component_start, input.len() as int)
                        == duration_parts_text(parts)
                );
            } else {
                assert(rank == 4);
                assert(input[index] == 'm');
                assert(input[index + 1] == 's');
                assert(next == index + 2);
                assert(
                    tail.d_days.len() == 0
                        && tail.d_hours.len() == 0
                        && tail.d_minutes.len() == 0
                        && tail.d_seconds.len() == 0
                        && tail.d_millis.len() == 0
                ) by {
                    reveal(duration_parts_after);
                }
                assert(input.subrange(component_start, input.len() as int)
                    == digits + seq!['m', 's'] + input.subrange(next, input.len() as int)) by {
                    assert_seqs_equal!(
                        input.subrange(component_start, input.len() as int)
                            == digits
                                + seq!['m', 's']
                                + input.subrange(next, input.len() as int)
                    );
                }
                reveal(duration_parts_text);
                reveal(duration_part_text);
                assert_seqs_equal!(
                    input.subrange(component_start, input.len() as int)
                        == duration_parts_text(parts)
                );
            }
            assert(duration_parts_after(parts, previous_rank)) by {
                reveal(duration_parts_after);
                reveal(duration_digits_wf);
            }
            assert(result == total + duration_parts_value(parts)) by {
                reveal(duration_parts_value);
            }
            assert(exists|candidate: DurationParts|
                input.subrange(component_start, input.len() as int)
                        == duration_parts_text(candidate)
                    && duration_parts_after(candidate, previous_rank)
                    && result == total + duration_parts_value(candidate)) by {
                assert(
                    input.subrange(component_start, input.len() as int)
                            == duration_parts_text(parts)
                        && duration_parts_after(parts, previous_rank)
                        && result == total + duration_parts_value(parts)
                );
            }
        }
    }
}

pub proof fn duration_parts_build_valid_view(
    input: Seq<char>,
    sign: Seq<char>,
    parts: DurationParts,
    value: int,
)
    requires
        input == sign + duration_parts_text(parts),
        sign.len() == 0 || sign == seq!['-'],
        duration_parts_after(parts, -1),
        1 <= duration_parts_text(parts).len(),
        value == triptych_sign_of(sign) * duration_parts_value(parts),
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        duration_is_valid(input),
        duration_matches_result(input, value),
{
    let days = duration_part_text(parts.d_days, 0);
    let hours = duration_part_text(parts.d_hours, 1);
    let minutes = duration_part_text(parts.d_minutes, 2);
    let seconds = duration_part_text(parts.d_seconds, 3);
    let millis = duration_part_text(parts.d_millis, 4);
    let components = duration_parts_text(parts);
    let view = DurationView {
        input,
        sign,
        d_days: parts.d_days,
        d_hours: parts.d_hours,
        d_minutes: parts.d_minutes,
        d_seconds: parts.d_seconds,
        d_millis: parts.d_millis,
        components,
    };
    reveal(duration_parts_after);
    reveal(duration_digits_wf);
    if parts.d_days.len() != 0 {
        assert(duration_matches_DDays(parts.d_days, view)) by {
            reveal(duration_matches_DDays);
        }
        assert(duration_matches_Days(days, view)) by {
            reveal(duration_part_text);
            reveal(duration_matches_Days);
        }
        assert(duration_is_wf_DDays(parts.d_days)) by {
            reveal(duration_is_wf_DDays);
        }
        assert(duration_is_wf_Days(days)) by {
            reveal(duration_part_text);
            reveal(duration_is_wf_Days);
        }
    }
    if parts.d_hours.len() != 0 {
        assert(duration_matches_DHours(parts.d_hours, view)) by {
            reveal(duration_matches_DHours);
        }
        assert(duration_matches_Hours(hours, view)) by {
            reveal(duration_part_text);
            reveal(duration_matches_Hours);
        }
        assert(duration_is_wf_DHours(parts.d_hours)) by {
            reveal(duration_is_wf_DHours);
        }
        assert(duration_is_wf_Hours(hours)) by {
            reveal(duration_part_text);
            reveal(duration_is_wf_Hours);
        }
    }
    if parts.d_minutes.len() != 0 {
        assert(duration_matches_DMinutes(parts.d_minutes, view)) by {
            reveal(duration_matches_DMinutes);
        }
        assert(duration_matches_Minutes(minutes, view)) by {
            reveal(duration_part_text);
            reveal(duration_matches_Minutes);
        }
        assert(duration_is_wf_DMinutes(parts.d_minutes)) by {
            reveal(duration_is_wf_DMinutes);
        }
        assert(duration_is_wf_Minutes(minutes)) by {
            reveal(duration_part_text);
            reveal(duration_is_wf_Minutes);
        }
    }
    if parts.d_seconds.len() != 0 {
        assert(duration_matches_DSeconds(parts.d_seconds, view)) by {
            reveal(duration_matches_DSeconds);
        }
        assert(duration_matches_Seconds(seconds, view)) by {
            reveal(duration_part_text);
            reveal(duration_matches_Seconds);
        }
        assert(duration_is_wf_DSeconds(parts.d_seconds)) by {
            reveal(duration_is_wf_DSeconds);
        }
        assert(duration_is_wf_Seconds(seconds)) by {
            reveal(duration_part_text);
            reveal(duration_is_wf_Seconds);
        }
    }
    if parts.d_millis.len() != 0 {
        assert(duration_matches_DMillis(parts.d_millis, view)) by {
            reveal(duration_matches_DMillis);
        }
        assert(duration_matches_Millis(millis, view)) by {
            reveal(duration_part_text);
            reveal(duration_matches_Millis);
        }
        assert(duration_is_wf_DMillis(parts.d_millis)) by {
            reveal(duration_is_wf_DMillis);
        }
        assert(duration_is_wf_Millis(millis)) by {
            reveal(duration_part_text);
            reveal(duration_is_wf_Millis);
        }
    }
    assert(components == days + hours + minutes + seconds + millis) by {
        reveal(duration_parts_text);
    }
    assert(duration_matches_Components(components, view)) by {
        reveal(duration_matches_Components);
        assert(exists|candidate_days: Seq<char>, candidate_hours: Seq<char>,
                candidate_minutes: Seq<char>, candidate_seconds: Seq<char>,
                candidate_millis: Seq<char>|
            components
                == candidate_days
                    + candidate_hours
                    + candidate_minutes
                    + candidate_seconds
                    + candidate_millis
                && (candidate_days.len() == 0 && view.d_days == seq![]
                    || duration_matches_Days(candidate_days, view))
                && (candidate_hours.len() == 0 && view.d_hours == seq![]
                    || duration_matches_Hours(candidate_hours, view))
                && (candidate_minutes.len() == 0 && view.d_minutes == seq![]
                    || duration_matches_Minutes(candidate_minutes, view))
                && (candidate_seconds.len() == 0 && view.d_seconds == seq![]
                    || duration_matches_Seconds(candidate_seconds, view))
                && (candidate_millis.len() == 0 && view.d_millis == seq![]
                    || duration_matches_Millis(candidate_millis, view))) by {
            assert(
                components == days + hours + minutes + seconds + millis
                    && (days.len() == 0 && view.d_days == seq![]
                        || duration_matches_Days(days, view))
                    && (hours.len() == 0 && view.d_hours == seq![]
                        || duration_matches_Hours(hours, view))
                    && (minutes.len() == 0 && view.d_minutes == seq![]
                        || duration_matches_Minutes(minutes, view))
                    && (seconds.len() == 0 && view.d_seconds == seq![]
                        || duration_matches_Seconds(seconds, view))
                    && (millis.len() == 0 && view.d_millis == seq![]
                        || duration_matches_Millis(millis, view))
            );
        }
    }
    assert(duration_is_wf_Components(components)) by {
        reveal(duration_is_wf_Components);
        assert(exists|candidate_days: Seq<char>, candidate_hours: Seq<char>,
                candidate_minutes: Seq<char>, candidate_seconds: Seq<char>,
                candidate_millis: Seq<char>|
            components
                == candidate_days
                    + candidate_hours
                    + candidate_minutes
                    + candidate_seconds
                    + candidate_millis
                && (candidate_days.len() == 0
                    || duration_is_wf_Days(candidate_days))
                && (candidate_hours.len() == 0
                    || duration_is_wf_Hours(candidate_hours))
                && (candidate_minutes.len() == 0
                    || duration_is_wf_Minutes(candidate_minutes))
                && (candidate_seconds.len() == 0
                    || duration_is_wf_Seconds(candidate_seconds))
                && (candidate_millis.len() == 0
                    || duration_is_wf_Millis(candidate_millis))) by {
            assert(
                components == days + hours + minutes + seconds + millis
                    && (days.len() == 0 || duration_is_wf_Days(days))
                    && (hours.len() == 0 || duration_is_wf_Hours(hours))
                    && (minutes.len() == 0 || duration_is_wf_Minutes(minutes))
                    && (seconds.len() == 0 || duration_is_wf_Seconds(seconds))
                    && (millis.len() == 0 || duration_is_wf_Millis(millis))
            );
        }
    }
    assert(duration_matches_Sign(sign, view)) by {
        reveal(duration_matches_Sign);
    }
    assert(duration_is_wf_Sign(sign)) by {
        reveal(duration_is_wf_Sign);
    }
    assert(duration_matches_Duration(input, view)) by {
        reveal(duration_matches_Duration);
        assert(exists|candidate_sign: Seq<char>, candidate_components: Seq<char>|
            input == candidate_sign + candidate_components
                && (view.sign == candidate_sign
                    && duration_matches_Sign(candidate_sign, view))
                && (view.components == candidate_components
                    && duration_matches_Components(candidate_components, view))) by {
            assert(
                input == sign + components
                    && (view.sign == sign && duration_matches_Sign(sign, view))
                    && (view.components == components
                        && duration_matches_Components(components, view))
            );
        }
    }
    assert(duration_matches_view(input, view)) by {
        reveal(duration_matches_view);
    }
    assert(duration_is_wf_Duration(input)) by {
        reveal(duration_is_wf_Duration);
        assert(exists|candidate_sign: Seq<char>, candidate_components: Seq<char>|
            input == candidate_sign + candidate_components
                && duration_is_wf_Sign(candidate_sign)
                && duration_is_wf_Components(candidate_components)) by {
            assert(
                input == sign + components
                    && duration_is_wf_Sign(sign)
                    && duration_is_wf_Components(components)
            );
        }
    }
    assert(duration_view_wf_constraints(view)) by {
        reveal(duration_view_wf_constraints);
        reveal(duration_wf_constraints);
    }
    assert(duration_view_denotation(view) == value) by {
        reveal(duration_view_denotation);
        reveal(duration_value);
        reveal(duration_parts_value);
    }
    assert(duration_view_constraints(view)) by {
        reveal(duration_view_constraints);
        reveal(duration_constraints);
    }
    assert(duration_view_valid(view)) by {
        reveal(duration_view_valid);
    }
    assert(duration_matches_result(input, value)) by {
        reveal(duration_matches_result);
        assert(exists|candidate: DurationView|
            duration_matches_view(input, candidate)
                && duration_view_valid(candidate)
                && duration_view_denotation(candidate) == value) by {
            assert(
                duration_matches_view(input, view)
                    && duration_view_valid(view)
                    && duration_view_denotation(view) == value
            );
        }
    }
    assert(duration_satisfies_wf_constraints(input)) by {
        reveal(duration_satisfies_wf_constraints);
        assert(exists|candidate: DurationView|
            duration_matches_view(input, candidate)
                && duration_view_wf_constraints(candidate)) by {
            assert(
                duration_matches_view(input, view)
                    && duration_view_wf_constraints(view)
            );
        }
    }
    assert(duration_satisfies_constraints(input)) by {
        reveal(duration_satisfies_constraints);
        assert(exists|candidate: DurationView|
            duration_matches_view(input, candidate)
                && duration_view_constraints(candidate)) by {
            assert(
                duration_matches_view(input, view)
                    && duration_view_constraints(view)
            );
        }
    }
    reveal(duration_is_valid);
    reveal(duration_is_wf);
}

pub proof fn duration_parse_spec_sound(input: Seq<char>, value: int)
    requires
        duration_parse_spec(input) == Some(value),
    ensures
        duration_is_valid(input),
        duration_matches_result(input, value),
{
    reveal(duration_parse_spec);
    assert(is_ascii_chars(input));
    assert(0 < input.len());
    let negative = input[0] == '-';
    let start: int = if negative { 1 } else { 0 };
    assert(start != input.len());
    let limit: int = if negative {
        9_223_372_036_854_775_808
    } else {
        9_223_372_036_854_775_807
    };
    match duration_parse_state(input, start, -1, 0, limit, 0, false) {
        Some(magnitude) => {
            let empty = Seq::<char>::empty();
            assert(triptych_nat_of(empty) == 0) by {
                reveal(triptych_nat_of);
                reveal_with_fuel(triptych_nat_of_from, 2);
            }
            duration_parse_state_sound_parts(
                input,
                start,
                start,
                -1,
                0,
                limit,
                0,
                false,
                magnitude,
            );
            let parts = choose|parts: DurationParts|
                input.subrange(start, input.len() as int) == duration_parts_text(parts)
                    && duration_parts_after(parts, -1)
                    && magnitude == duration_parts_value(parts);
            let sign = input.subrange(0, start);
            let components = input.subrange(start, input.len() as int);
            assert(input == sign + components) by {
                assert_seqs_equal!(input == sign + components);
            }
            if negative {
                assert(start == 1);
                assert(sign == seq!['-']) by {
                    assert_seqs_equal!(sign == seq!['-']);
                }
                assert(triptych_sign_of(sign) == -1) by {
                    reveal(triptych_sign_of);
                }
                assert(value == -magnitude);
                assert(magnitude <= 9_223_372_036_854_775_808);
            } else {
                assert(start == 0);
                assert(sign == empty) by {
                    assert_seqs_equal!(sign == empty);
                }
                assert(triptych_sign_of(sign) == 1) by {
                    reveal(triptych_sign_of);
                }
                assert(value == magnitude);
                assert(magnitude <= 9_223_372_036_854_775_807);
            }
            assert(0 <= magnitude);
            assert(-9_223_372_036_854_775_808
                <= value <= 9_223_372_036_854_775_807);
            assert(1 <= components.len());
            assert(value
                == triptych_sign_of(sign) * duration_parts_value(parts));
            duration_parts_build_valid_view(input, sign, parts, value);
        },
        None => {
            assert(false);
        },
    }
}

pub proof fn duration_has_result_bounds(value: int)
    requires
        duration_has_result(value),
    ensures
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
{
    reveal(duration_has_result);
    let input = choose|input: Seq<char>| duration_matches_result(input, value);
    reveal(duration_matches_result);
    let view = choose|view: DurationView|
        duration_matches_view(input, view)
            && duration_view_valid(view)
            && duration_view_denotation(view) == value;
    reveal(duration_view_valid);
    reveal(duration_view_constraints);
    reveal(duration_constraints);
    reveal(duration_view_denotation);
}

pub proof fn duration_canonical_matches_result(value: int)
    requires
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        duration_matches_result(duration_canonical_characters(value), value),
        duration_is_valid(duration_canonical_characters(value)),
{
    let magnitude = if value < 0 { -value } else { value };
    let sign = if value < 0 { seq!['-'] } else { Seq::<char>::empty() };
    let digits = duration_natural_characters(magnitude as nat);
    let components = digits + seq!['m', 's'];
    let view = DurationView {
        input: duration_canonical_characters(value),
        sign,
        d_days: seq![],
        d_hours: seq![],
        d_minutes: seq![],
        d_seconds: seq![],
        d_millis: digits,
        components,
    };
    assert(0 <= magnitude);
    duration_natural_characters_properties(magnitude as nat);
    assert(duration_matches_DMillis(digits, view)) by {
        reveal(duration_matches_DMillis);
    }
    assert(duration_matches_Millis(components, view)) by {
        reveal(duration_matches_Millis);
    }
    assert(duration_matches_Components(components, view)) by {
        reveal(duration_matches_Components);
        let empty = Seq::<char>::empty();
        assert(components == empty + empty + empty + empty + components);
        assert(exists|days: Seq<char>, hours: Seq<char>, minutes: Seq<char>,
                seconds: Seq<char>, millis: Seq<char>|
            components == days + hours + minutes + seconds + millis
                && (days.len() == 0 && view.d_days == seq![]
                    || duration_matches_Days(days, view))
                && (hours.len() == 0 && view.d_hours == seq![]
                    || duration_matches_Hours(hours, view))
                && (minutes.len() == 0 && view.d_minutes == seq![]
                    || duration_matches_Minutes(minutes, view))
                && (seconds.len() == 0 && view.d_seconds == seq![]
                    || duration_matches_Seconds(seconds, view))
                && (millis.len() == 0 && view.d_millis == seq![]
                    || duration_matches_Millis(millis, view))) by {
            assert(
                components == empty + empty + empty + empty + components
                    && (empty.len() == 0 && view.d_days == seq![]
                        || duration_matches_Days(empty, view))
                    && (empty.len() == 0 && view.d_hours == seq![]
                        || duration_matches_Hours(empty, view))
                    && (empty.len() == 0 && view.d_minutes == seq![]
                        || duration_matches_Minutes(empty, view))
                    && (empty.len() == 0 && view.d_seconds == seq![]
                        || duration_matches_Seconds(empty, view))
                    && (components.len() == 0 && view.d_millis == seq![]
                        || duration_matches_Millis(components, view))
            );
        }
    }
    assert(duration_matches_Sign(sign, view)) by {
        reveal(duration_matches_Sign);
    }
    assert(duration_canonical_characters(value) == sign + components) by {
        reveal(duration_canonical_characters);
        assert_seqs_equal!(
            duration_canonical_characters(value) == sign + components
        );
    }
    assert(duration_matches_Duration(duration_canonical_characters(value), view)) by {
        reveal(duration_matches_Duration);
        assert(exists|matched_sign: Seq<char>, matched_components: Seq<char>|
            duration_canonical_characters(value) == matched_sign + matched_components
                && (view.sign == matched_sign
                    && duration_matches_Sign(matched_sign, view))
                && (view.components == matched_components
                    && duration_matches_Components(matched_components, view))) by {
            assert(
                duration_canonical_characters(value) == sign + components
                    && (view.sign == sign && duration_matches_Sign(sign, view))
                    && (view.components == components
                        && duration_matches_Components(components, view))
            );
        }
    }
    assert(duration_matches_view(duration_canonical_characters(value), view)) by {
        reveal(duration_matches_view);
    }
    assert(duration_view_denotation(view) == value) by {
        reveal(duration_view_denotation);
        reveal(duration_value);
        assert(triptych_nat_of(digits) == magnitude);
        if value < 0 {
            assert(sign == seq!['-']);
            assert(triptych_sign_of(sign) == -1) by {
                reveal(triptych_sign_of);
            }
        } else {
            assert(sign == Seq::<char>::empty());
            assert(triptych_sign_of(sign) == 1) by {
                reveal(triptych_sign_of);
            }
        }
    }
    assert(duration_view_valid(view)) by {
        reveal(duration_view_valid);
        reveal(duration_view_wf_constraints);
        reveal(duration_wf_constraints);
        reveal(duration_view_constraints);
        reveal(duration_constraints);
        assert(1 <= components.len());
    }
    assert(duration_is_wf_DMillis(digits)) by {
        reveal(duration_is_wf_DMillis);
    }
    assert(duration_is_wf_Millis(components)) by {
        reveal(duration_is_wf_Millis);
    }
    assert(duration_is_wf_Components(components)) by {
        reveal(duration_is_wf_Components);
    }
    assert(duration_is_wf_Sign(sign)) by {
        reveal(duration_is_wf_Sign);
    }
    assert(duration_is_wf_Duration(duration_canonical_characters(value))) by {
        reveal(duration_canonical_characters);
        reveal(duration_is_wf_Duration);
    }
    assert(duration_satisfies_wf_constraints(duration_canonical_characters(value))) by {
        reveal(duration_satisfies_wf_constraints);
    }
    assert(duration_is_wf(duration_canonical_characters(value))) by {
        reveal(duration_is_wf);
    }
    assert(duration_satisfies_constraints(duration_canonical_characters(value))) by {
        reveal(duration_satisfies_constraints);
    }
    assert(duration_is_valid(duration_canonical_characters(value))) by {
        reveal(duration_is_valid);
    }
    reveal(duration_matches_result);
}

impl DurationExternalParserContract for DurationParser {
    open spec fn parse_to_spec(input: Seq<char>) -> Option<int> {
        duration_parse_spec(input)
    }

    proof fn extparse_sound(input: Seq<char>, value: int) {
        duration_parse_spec_sound(input, value);
    }

    proof fn extparse_complete(input: Seq<char>, value: int) {
        reveal(duration_matches_result);
        let view = choose|view: DurationView|
            duration_matches_view(input, view)
                && duration_view_valid(view)
                && duration_view_denotation(view) == value;
        duration_generated_view_parses(input, view);
    }

    proof fn extparse_reject(input: Seq<char>) {
        if Self::parse_to_spec(input).is_none() {
            if duration_is_valid(input) {
                duration_valid_has_result(input);
                let value = choose|value: int|
                    duration_matches_result(input, value);
                Self::extparse_complete(input, value);
                assert(false);
            }
        }
        if !duration_is_valid(input) {
            match Self::parse_to_spec(input) {
                Some(value) => {
                    Self::extparse_sound(input, value);
                    assert(false);
                },
                None => {},
            }
        }
    }

    open spec fn to_string_to_spec(value: int) -> Seq<char> {
        duration_canonical_characters(value)
    }

    proof fn extparse_to_string_roundtrip(value: int) {
        duration_has_result_bounds(value);
        duration_canonical_matches_result(value);
        Self::extparse_complete(duration_canonical_characters(value), value);
    }

    proof fn extparse_to_string_injective(left: int, right: int) {
        Self::extparse_to_string_roundtrip(left);
        Self::extparse_to_string_roundtrip(right);
    }

    proof fn extparse_normalize_eq_iff_parse_eq(left: Seq<char>, right: Seq<char>) {
        match Self::parse_to_spec(left) {
            Some(left_value) => {
                Self::extparse_sound(left, left_value);
                assert(duration_has_result(left_value)) by {
                    reveal(duration_has_result);
                    assert(duration_matches_result(left, left_value));
                }
                match Self::parse_to_spec(right) {
                    Some(right_value) => {
                        Self::extparse_sound(right, right_value);
                        assert(duration_has_result(right_value)) by {
                            reveal(duration_has_result);
                            assert(duration_matches_result(right, right_value));
                        }
                        if duration_canonical_characters(left_value)
                            == duration_canonical_characters(right_value) {
                            Self::extparse_to_string_injective(left_value, right_value);
                        }
                    },
                    None => {},
                }
            },
            None => {},
        }
    }
}

} // verus!
