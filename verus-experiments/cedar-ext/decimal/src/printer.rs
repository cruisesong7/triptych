#[cfg(verus_only)]
use vstd::arithmetic::div_mod::{
    lemma_div_decreases, lemma_div_pos_is_pos, lemma_fundamental_div_mod, lemma_mod_pos_bound,
};
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::contract::{decimal_has_result, decimal_matches_result};
#[cfg(verus_only)]
use crate::soundness::{
    decimal_external_parse_complete, decimal_external_parse_sound, decimal_external_parse_to_spec,
    decimal_has_result_bounds,
};
#[cfg(verus_only)]
use crate::spec::*;

verus! {

pub open spec fn decimal_digit_character(digit: nat) -> char
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

pub proof fn decimal_digit_character_properties(digit: nat)
    requires
        digit <= 9,
    ensures
        triptych_is_digit(decimal_digit_character(digit)),
        decimal_digit_character(digit) as int - TRIPTYCH_ZERO as int == digit as int,
{
    reveal(decimal_digit_character);
    reveal(triptych_is_digit);
}

fn decimal_digit_character_exec(digit: u64) -> (result: char)
    requires
        digit <= 9,
    ensures
        result == decimal_digit_character(digit as nat),
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

pub open spec fn decimal_natural_characters(value: nat) -> Seq<char>
    decreases value,
{
    if value < 10 {
        seq![decimal_digit_character(value)]
    } else {
        decimal_natural_characters(value / 10).push(
            decimal_digit_character(value % 10),
        )
    }
}

pub proof fn triptych_nat_of_from_push_digit(
    characters: Seq<char>,
    index: int,
    accumulator: int,
    digit: nat,
)
    requires
        0 <= index <= characters.len(),
        digit <= 9,
    ensures
        triptych_nat_of_from(
            characters.push(decimal_digit_character(digit)),
            index,
            accumulator,
        ) == triptych_nat_of_from(characters, index, accumulator) * 10 + digit,
    decreases characters.len() - index,
{
    decimal_digit_character_properties(digit);
    let character = decimal_digit_character(digit);
    if index < characters.len() {
        assert(characters.push(character)[index] == characters[index]);
        triptych_nat_of_from_push_digit(
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
        assert(characters.push(character)[index] == character);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
}

pub proof fn decimal_natural_characters_properties(value: nat)
    ensures
        1 <= decimal_natural_characters(value).len(),
        forall|index: int| 0 <= index < decimal_natural_characters(value).len() ==>
            #[trigger] triptych_is_digit(decimal_natural_characters(value)[index]),
        triptych_nat_of(decimal_natural_characters(value)) == value,
    decreases value,
{
    reveal(decimal_natural_characters);
    if value < 10 {
        decimal_digit_character_properties(value);
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    } else {
        let quotient = value / 10;
        let remainder = value % 10;
        lemma_div_decreases(value as int, 10);
        lemma_mod_pos_bound(value as int, 10);
        lemma_fundamental_div_mod(value as int, 10);
        decimal_natural_characters_properties(quotient);
        decimal_digit_character_properties(remainder);
        triptych_nat_of_from_push_digit(
            decimal_natural_characters(quotient),
            0,
            0,
            remainder,
        );
        reveal(triptych_nat_of);
        assert forall|index: int|
            0 <= index < decimal_natural_characters(quotient).push(
                decimal_digit_character(remainder),
            ).len() implies
                #[trigger] triptych_is_digit(
                    decimal_natural_characters(quotient).push(
                        decimal_digit_character(remainder),
                    )[index],
                ) by {
            if index < decimal_natural_characters(quotient).len() {
                assert(
                    decimal_natural_characters(quotient).push(
                        decimal_digit_character(remainder),
                    )[index]
                        == decimal_natural_characters(quotient)[index]
                );
            } else {
                assert(index == decimal_natural_characters(quotient).len());
                assert(
                    decimal_natural_characters(quotient).push(
                        decimal_digit_character(remainder),
                    )[index]
                        == decimal_digit_character(remainder)
                );
            }
        }
    }
}

fn decimal_push_natural(output: &mut String, value: u64)
    requires
        value <= 922_337_203_685_477,
    ensures
        final(output)@ == old(output)@ + decimal_natural_characters(value as nat),
    decreases value,
{
    if value >= 10 {
        proof {
            lemma_div_decreases(value as int, 10);
        }
        decimal_push_natural(output, value / 10);
    }
    let digit = value % 10;
    proof {
        lemma_mod_pos_bound(value as int, 10);
    }
    output.push(decimal_digit_character_exec(digit));
}

pub open spec fn decimal_fraction_characters(value: nat) -> Seq<char>
    recommends
        value < 10_000,
{
    seq![
        decimal_digit_character(value / 1_000),
        decimal_digit_character((value / 100) % 10),
        decimal_digit_character((value / 10) % 10),
        decimal_digit_character(value % 10),
    ]
}

pub proof fn decimal_fraction_characters_properties(value: nat)
    requires
        value < 10_000,
    ensures
        decimal_fraction_characters(value).len() == 4,
        forall|index: int| 0 <= index < 4 ==>
            #[trigger] triptych_is_digit(decimal_fraction_characters(value)[index]),
        triptych_nat_of(decimal_fraction_characters(value)) == value,
{
    lemma_mod_pos_bound(value as int, 10);
    lemma_mod_pos_bound((value / 10) as int, 10);
    lemma_mod_pos_bound((value / 100) as int, 10);
    lemma_fundamental_div_mod(value as int, 10);
    lemma_fundamental_div_mod((value / 10) as int, 10);
    lemma_fundamental_div_mod((value / 100) as int, 10);
    lemma_fundamental_div_mod((value / 1_000) as int, 10);
    decimal_digit_character_properties(value / 1_000);
    decimal_digit_character_properties((value / 100) % 10);
    decimal_digit_character_properties((value / 10) % 10);
    decimal_digit_character_properties(value % 10);
    reveal(decimal_fraction_characters);
    reveal(triptych_nat_of);
    reveal_with_fuel(triptych_nat_of_from, 5);
}

fn decimal_push_fraction(output: &mut String, value: u64)
    requires
        value < 10_000,
    ensures
        final(output)@ == old(output)@ + decimal_fraction_characters(value as nat),
{
    let thousands = value / 1_000;
    let hundreds = (value / 100) % 10;
    let tens = (value / 10) % 10;
    let ones = value % 10;
    proof {
        lemma_mod_pos_bound((value / 100) as int, 10);
        lemma_mod_pos_bound((value / 10) as int, 10);
        lemma_mod_pos_bound(value as int, 10);
        assert(thousands <= 9);
        reveal(decimal_fraction_characters);
    }
    output.push(decimal_digit_character_exec(thousands));
    output.push(decimal_digit_character_exec(hundreds));
    output.push(decimal_digit_character_exec(tens));
    output.push(decimal_digit_character_exec(ones));
}

pub open spec fn decimal_canonical_characters(value: int) -> Seq<char>
    recommends
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
{
    let magnitude = if value < 0 { -value } else { value };
    let sign = if value < 0 { seq!['-'] } else { Seq::<char>::empty() };
    sign
        + decimal_natural_characters((magnitude / 10_000) as nat)
        + seq!['.']
        + decimal_fraction_characters((magnitude % 10_000) as nat)
}

pub struct DecimalPrinter {}

impl DecimalPrinter {
    /** Cedar-compatible canonical Decimal rendering with exactly four fractional digits. */
    pub fn to_string(value: i64) -> (result: String)
        ensures
            result@ == decimal_canonical_characters(value as int),
            decimal_matches_result(result@, value as int),
            decimal_external_parse_to_spec(result@) == Some(value as int),
    {
        let negative = value < 0;
        let magnitude = if value == i64::MIN {
            9_223_372_036_854_775_808u64
        } else if negative {
            (-value) as u64
        } else {
            value as u64
        };
        let natural = magnitude / 10_000;
        let fraction = magnitude % 10_000;
        let mut result = String::new();
        if negative {
            result.push('-');
        }
        decimal_push_natural(&mut result, natural);
        result.push('.');
        decimal_push_fraction(&mut result, fraction);
        proof {
            lemma_fundamental_div_mod(magnitude as int, 10_000);
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
            assert(
                (natural as int) * 10_000 + fraction as int == magnitude as int
            );
            decimal_natural_characters_properties(natural as nat);
            decimal_fraction_characters_properties(fraction as nat);
            let sign = if negative { seq!['-'] } else { Seq::<char>::empty() };
            let view = DecimalView {
                input: result@,
                sign,
                natural: decimal_natural_characters(natural as nat),
                fraction: decimal_fraction_characters(fraction as nat),
            };
            assert(result@ == decimal_canonical_characters(value as int)) by {
                reveal(decimal_canonical_characters);
            }
            assert(decimal_matches_view(result@, view)) by {
                reveal(decimal_matches_view);
                reveal(decimal_is_wf_Sign);
                reveal(decimal_is_wf_Natural);
                reveal(decimal_is_wf_Fraction);
            }
            assert(decimal_view_denotation(view) == value as int) by {
                reveal(decimal_view_denotation);
                reveal(decimal_value);
                reveal_with_fuel(triptych_int_pow, 5);
                assert(triptych_int_pow(10, 4) == 10_000);
                assert(triptych_nat_of(view.natural) == natural as int);
                assert(triptych_nat_of(view.fraction) == fraction as int);
                assert(view.fraction.len() == 4);
                assert(triptych_int_pow(10, 4 - view.fraction.len() as int) == 1);
                if negative {
                    assert(sign == seq!['-']);
                    assert(triptych_sign_of(view.sign) == -1) by {
                        reveal(triptych_sign_of);
                    }
                } else {
                    assert(sign == Seq::<char>::empty());
                    assert(triptych_sign_of(view.sign) == 1) by {
                        reveal(triptych_sign_of);
                    }
                }
            }
            assert(decimal_view_valid(view)) by {
                reveal(decimal_view_valid);
                reveal(decimal_view_constraints);
                reveal(decimal_constraints);
            }
            assert(decimal_matches_result(result@, value as int)) by {
                reveal(decimal_matches_result);
            }
            decimal_external_parse_complete(result@, value as int);
        }
        result
    }
}

pub proof fn decimal_extparse_to_string_roundtrip(value: int)
    requires
        decimal_has_result(value),
    ensures
        decimal_external_parse_to_spec(decimal_canonical_characters(value)) == Some(value),
{
    decimal_has_result_bounds(value);
    let magnitude = if value < 0 { -value } else { value };
    let natural = magnitude / 10_000;
    let fraction = magnitude % 10_000;
    let sign = if value < 0 { seq!['-'] } else { Seq::<char>::empty() };
    let view = DecimalView {
        input: decimal_canonical_characters(value),
        sign,
        natural: decimal_natural_characters(natural as nat),
        fraction: decimal_fraction_characters(fraction as nat),
    };
    assert(0 <= magnitude);
    lemma_div_pos_is_pos(magnitude, 10_000);
    lemma_fundamental_div_mod(magnitude, 10_000);
    lemma_mod_pos_bound(magnitude, 10_000);
    assert(0 <= natural);
    assert(0 <= fraction < 10_000);
    assert(natural * 10_000 + fraction == magnitude);
    decimal_natural_characters_properties(natural as nat);
    decimal_fraction_characters_properties(fraction as nat);
    assert(triptych_nat_of(decimal_natural_characters(natural as nat)) == natural);
    assert(triptych_nat_of(decimal_fraction_characters(fraction as nat)) == fraction);
    assert(decimal_matches_view(decimal_canonical_characters(value), view)) by {
        reveal(decimal_canonical_characters);
        reveal(decimal_matches_view);
        reveal(decimal_is_wf_Sign);
        reveal(decimal_is_wf_Natural);
        reveal(decimal_is_wf_Fraction);
    }
    assert(decimal_view_denotation(view) == value) by {
        reveal(decimal_view_denotation);
        reveal(decimal_value);
        reveal_with_fuel(triptych_int_pow, 5);
        assert(view.fraction.len() == 4);
        assert(triptych_int_pow(10, 4 - view.fraction.len() as int) == 1);
        if value < 0 {
            assert(sign == seq!['-']);
            assert(triptych_sign_of(view.sign) == -1) by {
                reveal(triptych_sign_of);
            }
        } else {
            assert(sign == Seq::<char>::empty());
            assert(triptych_sign_of(view.sign) == 1) by {
                reveal(triptych_sign_of);
            }
        }
    }
    assert(decimal_view_valid(view)) by {
        reveal(decimal_view_valid);
        reveal(decimal_view_constraints);
        reveal(decimal_constraints);
    }
    assert(decimal_matches_result(decimal_canonical_characters(value), value)) by {
        reveal(decimal_matches_result);
    }
    decimal_external_parse_complete(decimal_canonical_characters(value), value);
}

pub proof fn decimal_extparse_to_string_injective(left: int, right: int)
    requires
        decimal_has_result(left),
        decimal_has_result(right),
        decimal_canonical_characters(left) == decimal_canonical_characters(right),
    ensures
        left == right,
{
    decimal_extparse_to_string_roundtrip(left);
    decimal_extparse_to_string_roundtrip(right);
}

pub open spec fn decimal_external_normalize(input: Seq<char>) -> Option<Seq<char>> {
    match decimal_external_parse_to_spec(input) {
        Some(value) => Some(decimal_canonical_characters(value)),
        None => None,
    }
}

pub proof fn decimal_extparse_normalize_eq_iff_parse_eq(
    left: Seq<char>,
    right: Seq<char>,
)
    ensures
        decimal_external_normalize(left) == decimal_external_normalize(right)
            <==> decimal_external_parse_to_spec(left) == decimal_external_parse_to_spec(right),
{
    reveal(decimal_external_normalize);
    match decimal_external_parse_to_spec(left) {
        Some(left_value) => {
            decimal_external_parse_sound(left, left_value);
            assert(decimal_has_result(left_value)) by {
                reveal(decimal_has_result);
                assert(decimal_matches_result(left, left_value));
            }
            match decimal_external_parse_to_spec(right) {
                Some(right_value) => {
                    decimal_external_parse_sound(right, right_value);
                    assert(decimal_has_result(right_value)) by {
                        reveal(decimal_has_result);
                        assert(decimal_matches_result(right, right_value));
                    }
                    if decimal_canonical_characters(left_value)
                        == decimal_canonical_characters(right_value) {
                        decimal_extparse_to_string_injective(left_value, right_value);
                    }
                },
                None => {},
            }
        },
        None => {},
    }
}

} // verus!
