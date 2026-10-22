#[cfg(verus_only)]
use vstd::arithmetic::div_mod::{
    lemma_div_decreases, lemma_fundamental_div_mod, lemma_mod_pos_bound,
};
use vstd::prelude::*;

verus! {

pub open spec fn duration_digit_character(digit: nat) -> char
    recommends
        digit <= 9,
{
    if digit == 0 {
        '0'
    } else if digit == 1 {
        '1'
    } else if digit == 2 {
        '2'
    } else if digit == 3 {
        '3'
    } else if digit == 4 {
        '4'
    } else if digit == 5 {
        '5'
    } else if digit == 6 {
        '6'
    } else if digit == 7 {
        '7'
    } else if digit == 8 {
        '8'
    } else {
        '9'
    }
}

pub proof fn duration_digit_character_properties(digit: nat)
    requires
        digit <= 9,
    ensures
        crate::spec::triptych_is_digit(duration_digit_character(digit)),
        duration_digit_character(digit) as int - crate::spec::TRIPTYCH_ZERO as int
            == digit as int,
{
    reveal(duration_digit_character);
    reveal(crate::spec::triptych_is_digit);
}

fn duration_digit_character_exec(digit: u64) -> (result: char)
    requires
        digit <= 9,
    ensures
        result == duration_digit_character(digit as nat),
{
    if digit == 0 {
        '0'
    } else if digit == 1 {
        '1'
    } else if digit == 2 {
        '2'
    } else if digit == 3 {
        '3'
    } else if digit == 4 {
        '4'
    } else if digit == 5 {
        '5'
    } else if digit == 6 {
        '6'
    } else if digit == 7 {
        '7'
    } else if digit == 8 {
        '8'
    } else {
        '9'
    }
}

pub open spec fn duration_natural_characters(value: nat) -> Seq<char>
    decreases value,
{
    if value < 10 {
        seq![duration_digit_character(value)]
    } else {
        duration_natural_characters(value / 10).push(
            duration_digit_character(value % 10),
        )
    }
}

pub proof fn triptych_nat_of_from_push_duration_digit(
    characters: Seq<char>,
    index: int,
    accumulator: int,
    digit: nat,
)
    requires
        0 <= index <= characters.len(),
        digit <= 9,
    ensures
        crate::spec::triptych_nat_of_from(
            characters.push(duration_digit_character(digit)),
            index,
            accumulator,
        ) == crate::spec::triptych_nat_of_from(characters, index, accumulator) * 10 + digit,
    decreases characters.len() - index,
{
    duration_digit_character_properties(digit);
    let character = duration_digit_character(digit);
    if index < characters.len() {
        assert(characters.push(character)[index] == characters[index]);
        triptych_nat_of_from_push_duration_digit(
            characters,
            index + 1,
            accumulator * 10
                + if (characters[index] as int) < (crate::spec::TRIPTYCH_ZERO as int) {
                    0
                } else {
                    (characters[index] as int) - (crate::spec::TRIPTYCH_ZERO as int)
                },
            digit,
        );
        reveal(crate::spec::triptych_nat_of_from);
    } else {
        assert(index == characters.len());
        assert(characters.push(character)[index] == character);
        reveal_with_fuel(crate::spec::triptych_nat_of_from, 2);
    }
}

pub proof fn duration_natural_characters_properties(value: nat)
    ensures
        1 <= duration_natural_characters(value).len(),
        forall|index: int| 0 <= index < duration_natural_characters(value).len() ==>
            #[trigger] crate::spec::triptych_is_digit(
                duration_natural_characters(value)[index],
            ),
        crate::spec::triptych_nat_of(duration_natural_characters(value)) == value,
    decreases value,
{
    reveal(duration_natural_characters);
    if value < 10 {
        duration_digit_character_properties(value);
        reveal(crate::spec::triptych_nat_of);
        reveal_with_fuel(crate::spec::triptych_nat_of_from, 2);
    } else {
        let quotient = value / 10;
        let remainder = value % 10;
        lemma_div_decreases(value as int, 10);
        lemma_mod_pos_bound(value as int, 10);
        lemma_fundamental_div_mod(value as int, 10);
        duration_natural_characters_properties(quotient);
        duration_digit_character_properties(remainder);
        triptych_nat_of_from_push_duration_digit(
            duration_natural_characters(quotient),
            0,
            0,
            remainder,
        );
        reveal(crate::spec::triptych_nat_of);
        assert forall|index: int|
            0 <= index < duration_natural_characters(quotient).push(
                duration_digit_character(remainder),
            ).len() implies
                #[trigger] crate::spec::triptych_is_digit(
                    duration_natural_characters(quotient).push(
                        duration_digit_character(remainder),
                    )[index],
                ) by {
            if index < duration_natural_characters(quotient).len() {
                assert(
                    duration_natural_characters(quotient).push(
                        duration_digit_character(remainder),
                    )[index]
                        == duration_natural_characters(quotient)[index]
                );
            } else {
                assert(index == duration_natural_characters(quotient).len());
                assert(
                    duration_natural_characters(quotient).push(
                        duration_digit_character(remainder),
                    )[index]
                        == duration_digit_character(remainder)
                );
            }
        }
    }
}

fn duration_push_natural(output: &mut String, value: u64)
    requires
        value <= 9_223_372_036_854_775_808,
    ensures
        final(output)@ == old(output)@ + duration_natural_characters(value as nat),
    decreases value,
{
    if value >= 10 {
        proof {
            lemma_div_decreases(value as int, 10);
        }
        duration_push_natural(output, value / 10);
    }
    let digit = value % 10;
    proof {
        lemma_mod_pos_bound(value as int, 10);
    }
    output.push(duration_digit_character_exec(digit));
}

pub open spec fn duration_canonical_characters(value: int) -> Seq<char>
    recommends
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
{
    let magnitude = if value < 0 { -value } else { value };
    let sign = if value < 0 { seq!['-'] } else { Seq::<char>::empty() };
    sign + duration_natural_characters(magnitude as nat) + seq!['m', 's']
}

pub struct DurationPrinter {}

impl DurationPrinter {
    /** Cedar-compatible canonical Duration rendering as signed milliseconds. */
    pub fn to_string(value: i64) -> (result: String)
        ensures
            result@ == duration_canonical_characters(value as int),
    {
        let negative = value < 0;
        let magnitude = if value == i64::MIN {
            9_223_372_036_854_775_808u64
        } else if negative {
            (-value) as u64
        } else {
            value as u64
        };
        let mut result = String::new();
        if negative {
            result.push('-');
        }
        duration_push_natural(&mut result, magnitude);
        result.push('m');
        result.push('s');
        proof {
            assert(magnitude as int
                == if negative { -(value as int) } else { value as int }) by {
                if value == i64::MIN {
                    assert(negative);
                    assert(value as int == -9_223_372_036_854_775_808);
                } else if negative {
                    assert(value < 0);
                } else {
                    assert(0 <= value);
                }
            }
            reveal(duration_canonical_characters);
        }
        result
    }
}

} // verus!
