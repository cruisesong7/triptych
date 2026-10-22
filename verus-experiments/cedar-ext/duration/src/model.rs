// Parser-local recursive proof model.
//
// This is not the generated specification boundary. The generated Triptych specification is in
// `spec.rs`; soundness proves this model equivalent to that generated specification.

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::utf8::is_ascii_chars;

verus! {

pub open spec fn duration_is_digit(character: char) -> bool {
    '0' <= character && character <= '9'
}

pub open spec fn duration_digit_value(character: char) -> int {
    if duration_is_digit(character) {
        character as int - '0' as int
    } else {
        0
    }
}

pub open spec fn duration_unit_rank(input: Seq<char>, index: int) -> int {
    if 0 <= index < input.len() && input[index] == 'd' {
        0
    } else if 0 <= index < input.len() && input[index] == 'h' {
        1
    } else if 0 <= index
        && index + 1 < input.len()
        && input[index] == 'm'
        && input[index + 1] == 's'
    {
        4
    } else if 0 <= index < input.len() && input[index] == 'm' {
        2
    } else if 0 <= index < input.len() && input[index] == 's' {
        3
    } else {
        -1
    }
}

pub open spec fn duration_unit_length(input: Seq<char>, index: int) -> int {
    if 0 <= index
        && index + 1 < input.len()
        && input[index] == 'm'
        && input[index + 1] == 's'
    {
        2
    } else {
        1
    }
}

pub open spec fn duration_unit_multiplier(rank: int) -> int {
    if rank == 0 {
        86_400_000
    } else if rank == 1 {
        3_600_000
    } else if rank == 2 {
        60_000
    } else if rank == 3 {
        1_000
    } else {
        1
    }
}

pub open spec fn duration_parse_state(
    input: Seq<char>,
    index: int,
    previous_rank: int,
    total: int,
    limit: int,
    quantity: int,
    in_digits: bool,
) -> Option<int>
    decreases input.len() - index,
{
    if index < 0
        || index > input.len()
        || previous_rank < -1
        || previous_rank > 4
        || total < 0
        || total > limit
        || quantity < 0
        || quantity > 9_223_372_036_854_775_808
        || !(limit == 9_223_372_036_854_775_807
            || limit == 9_223_372_036_854_775_808)
    {
        None
    } else if index == input.len() {
        if !in_digits && 0 <= previous_rank {
            Some(total)
        } else {
            None
        }
    } else if duration_is_digit(input[index]) {
        let next_quantity = quantity * 10 + duration_digit_value(input[index]);
        if next_quantity > 9_223_372_036_854_775_808 {
            None
        } else {
            duration_parse_state(
                input,
                index + 1,
                previous_rank,
                total,
                limit,
                next_quantity,
                true,
            )
        }
    } else if !in_digits {
        None
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
            None
        } else {
            duration_parse_state(
                input,
                next,
                rank,
                total + contribution,
                limit,
                0,
                false,
            )
        }
    }
}

pub open spec fn duration_parse_spec(input: Seq<char>) -> Option<int> {
    if !is_ascii_chars(input) || input.len() == 0 {
        None
    } else {
        let negative = input[0] == '-';
        let start = if negative { 1 } else { 0 };
        if start == input.len() {
            None
        } else {
            let limit = if negative {
                9_223_372_036_854_775_808
            } else {
                9_223_372_036_854_775_807
            };
            match duration_parse_state(input, start, -1, 0, limit, 0, false) {
                Some(value) => if negative { Some(-value) } else { Some(value) },
                None => None,
            }
        }
    }
}

pub open spec fn duration_is_valid(input: Seq<char>) -> bool {
    duration_parse_spec(input).is_some()
}

} // verus!
