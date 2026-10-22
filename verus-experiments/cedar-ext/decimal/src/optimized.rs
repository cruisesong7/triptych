// Handwritten production parser proved against Triptych's generated Verus specification.

#[cfg(verus_only)]
use crate::parser::{
    decimal_four_digits_bound, decimal_is_wf_implies_parse_plan, decimal_parse_plan,
    decimal_parse_view, decimal_semantic_parse_plan, decimal_semantic_parse_plan_iff_valid,
    plan_scan_token_end_at_boundary, plan_token_accepts, PlanTokenClass,
};
use crate::parser::{DecimalParseSpec, DECIMAL_NATURAL_LIMIT};
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::{lemma_mul_basics, lemma_mul_unary_negation};
#[cfg(verus_only)]
use vstd::assert_seqs_equal;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::is_ascii_spec_bytes;
use vstd::string::StrSliceExecFns;

verus! {

pub struct DecimalParser;

#[derive(Copy, Clone)]
pub struct DecimalScanResult {
    pub end: usize,
    pub sign_start: usize,
    pub sign_end: usize,
    pub natural_start: usize,
    pub natural_end: usize,
    pub fraction_start: usize,
    pub fraction_end: usize,
    pub natural: u64,
    pub natural_overflow: bool,
    pub fraction: u64,
}

impl DeepView for DecimalScanResult {
    type V = DecimalParseSpec;

    open spec fn deep_view(&self) -> DecimalParseSpec {
        DecimalParseSpec {
            end: self.end as int,
            sign_start: self.sign_start as int,
            sign_end: self.sign_end as int,
            natural_start: self.natural_start as int,
            natural_end: self.natural_end as int,
            fraction_start: self.fraction_start as int,
            fraction_end: self.fraction_end as int,
        }
    }
}

#[inline(always)]
fn decimal_is_digit_at(input: &str, index: usize) -> (result: bool)
    requires
        input.is_ascii(),
        index < input@.len(),
    ensures
        result
            == plan_token_accepts(
                PlanTokenClass::Digit,
                input@[index as int],
            ),
{
    let byte = input.get_ascii(index);
    byte >= b'0' && byte <= b'9'
}

pub proof fn decimal_triptych_nat_of_from_push_digit(
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
        decimal_triptych_nat_of_from_push_digit(
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

pub proof fn decimal_triptych_nat_of_push_digit(
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
    decimal_triptych_nat_of_from_push_digit(characters, 0, 0, digit);
    reveal(triptych_nat_of);
}

#[inline]
fn decimal_scan(input: &str) -> (result: Option<DecimalScanResult>)
    ensures
        match result {
            Some(parsed) =>
                decimal_parse_plan(input@) == Some(parsed.deep_view())
                    && decimal_is_wf_Decimal(input@)
                    && decimal_matches_view(
                        input@,
                        decimal_parse_view(input@, parsed.deep_view()),
                    )
                    && parsed.natural <= DECIMAL_NATURAL_LIMIT
                    && parsed.fraction <= 9999
                    && if parsed.natural_overflow {
                        DECIMAL_NATURAL_LIMIT
                            < triptych_nat_of(
                                input@.subrange(
                                    parsed.natural_start as int,
                                    parsed.natural_end as int,
                                ),
                            )
                    } else {
                        triptych_nat_of(
                            input@.subrange(
                                parsed.natural_start as int,
                                parsed.natural_end as int,
                            ),
                        ) == parsed.natural as int
                            && parsed.natural <= DECIMAL_NATURAL_LIMIT
                    }
                    && triptych_nat_of(
                        input@.subrange(
                            parsed.fraction_start as int,
                            parsed.fraction_end as int,
                        ),
                    ) == parsed.fraction as int,
            None =>
                decimal_parse_plan(input@).is_none()
                    && !decimal_is_wf_Decimal(input@),
        },
{
    proof {
        if decimal_is_wf_Decimal(input@) {
            decimal_is_wf_implies_parse_plan(input@);
        }
    }
    if !input.is_ascii() {
        return None;
    }
    proof {
        broadcast use is_ascii_spec_bytes;
    }
    let length = input.unicode_len();
    let sign_start = 0usize;
    let sign_end =
        if length > 0 && input.get_ascii(0) == b'-' {
            1usize
        } else {
            0usize
        };
    let natural_start = sign_end;
    let mut index = natural_start;
    let mut natural = 0u64;
    let mut natural_overflow = false;
    let ghost mut natural_exact = 0int;

    while index < length && decimal_is_digit_at(input, index)
        invariant
            input.is_ascii(),
            length == input@.len(),
            natural_start <= index <= length,
            0 <= natural_exact,
            triptych_nat_of(
                input@.subrange(natural_start as int, index as int),
            ) == natural_exact,
            natural_overflow
                ==> DECIMAL_NATURAL_LIMIT < natural_exact,
            natural <= DECIMAL_NATURAL_LIMIT,
            !natural_overflow
                ==> natural_exact == natural as int
                    && natural <= DECIMAL_NATURAL_LIMIT,
            forall|position: int|
                natural_start <= position < index ==>
                    #[trigger] plan_token_accepts(
                        PlanTokenClass::Digit,
                        input@[position],
                    ),
        decreases length - index,
    {
        let byte = input.get_ascii(index);
        let digit = byte - b'0';
        assert(digit <= 9);
        let ghost previous_digits =
            input@.subrange(natural_start as int, index as int);
        let ghost next_digits =
            input@.subrange(natural_start as int, index as int + 1);
        let ghost next_exact = natural_exact * 10 + digit as int;
        proof {
            assert(plan_token_accepts(
                PlanTokenClass::Digit,
                input@[index as int],
            ));
            reveal(plan_token_accepts);
            assert(triptych_is_digit(input@[index as int])) by {
                reveal(triptych_is_digit);
            }
            assert(
                input@[index as int] as int - TRIPTYCH_ZERO as int
                    == digit as int
            );
            assert(next_digits =~= previous_digits.push(input@[index as int])) by {
                assert_seqs_equal!(
                    next_digits == previous_digits.push(input@[index as int])
                );
            }
            decimal_triptych_nat_of_push_digit(
                previous_digits,
                input@[index as int],
            );
            assert(triptych_nat_of(next_digits) == next_exact);
        }
        if !natural_overflow {
            assert(
                natural * 10 + digit as u64
                    <= 9_223_372_036_854_779u64
            );
            let next = natural * 10 + digit as u64;
            if next > DECIMAL_NATURAL_LIMIT {
                natural_overflow = true;
            } else {
                natural = next;
            }
        }
        proof {
            natural_exact = next_exact;
        }
        index += 1;
    }

    if index < length {
        assert(!plan_token_accepts(
            PlanTokenClass::Digit,
            input@[index as int],
        ));
    }
    proof {
        plan_scan_token_end_at_boundary(
            input@,
            natural_start as int,
            index as int,
            length as int,
            PlanTokenClass::Digit,
        );
    }
    if index == natural_start {
        reveal(decimal_parse_plan);
        return None;
    }
    let natural_end = index;
    if index == length || input.get_ascii(index) != b'.' {
        reveal(decimal_parse_plan);
        return None;
    }

    index += 1;
    let fraction_start = index;
    let mut fraction = 0u64;
    let ghost mut fraction_exact = 0int;

    while index < length && decimal_is_digit_at(input, index)
        invariant
            input.is_ascii(),
            length == input@.len(),
            fraction_start <= index <= length,
            0 <= fraction_exact,
            fraction <= 9999,
            triptych_nat_of(
                input@.subrange(fraction_start as int, index as int),
            ) == fraction_exact,
            index - fraction_start <= 4
                ==> fraction_exact == fraction as int,
            forall|position: int|
                fraction_start <= position < index ==>
                    #[trigger] plan_token_accepts(
                        PlanTokenClass::Digit,
                        input@[position],
                    ),
        decreases length - index,
    {
        let byte = input.get_ascii(index);
        let digit = byte - b'0';
        assert(digit <= 9);
        let ghost previous_digits =
            input@.subrange(fraction_start as int, index as int);
        let ghost next_digits =
            input@.subrange(fraction_start as int, index as int + 1);
        let ghost next_exact = fraction_exact * 10 + digit as int;
        proof {
            assert(plan_token_accepts(
                PlanTokenClass::Digit,
                input@[index as int],
            ));
            reveal(plan_token_accepts);
            assert(triptych_is_digit(input@[index as int])) by {
                reveal(triptych_is_digit);
            }
            assert(
                input@[index as int] as int - TRIPTYCH_ZERO as int
                    == digit as int
            );
            assert(next_digits =~= previous_digits.push(input@[index as int])) by {
                assert_seqs_equal!(
                    next_digits == previous_digits.push(input@[index as int])
                );
            }
            decimal_triptych_nat_of_push_digit(
                previous_digits,
                input@[index as int],
            );
            assert(triptych_nat_of(next_digits) == next_exact);
        }
        if index - fraction_start < 4 {
            let next = fraction * 10 + digit as u64;
            proof {
                assert(next_digits.len() <= 4);
                assert forall|position: int|
                    0 <= position < next_digits.len() implies
                        #[trigger] triptych_is_digit(next_digits[position]) by {
                    let source = fraction_start as int + position;
                    assert(next_digits[position] == input@[source]);
                    if source < index as int {
                        assert(plan_token_accepts(
                            PlanTokenClass::Digit,
                            input@[source],
                        ));
                        reveal(plan_token_accepts);
                        reveal(triptych_is_digit);
                    } else {
                        assert(source == index as int);
                    }
                }
                decimal_four_digits_bound(next_digits);
                assert(next as int == next_exact);
                assert(next <= 9999);
            }
            fraction = next;
        }
        proof {
            fraction_exact = next_exact;
        }
        index += 1;
    }

    if index < length {
        assert(!plan_token_accepts(
            PlanTokenClass::Digit,
            input@[index as int],
        ));
    }
    proof {
        plan_scan_token_end_at_boundary(
            input@,
            fraction_start as int,
            index as int,
            length as int,
            PlanTokenClass::Digit,
        );
    }
    let fraction_end = index;
    if fraction_end == fraction_start
        || fraction_end - fraction_start > 4
        || fraction_end != length
    {
        reveal(decimal_parse_plan);
        return None;
    }

    proof {
        let sign = input@.subrange(sign_start as int, sign_end as int);
        let natural =
            input@.subrange(natural_start as int, natural_end as int);
        let fraction_digits =
            input@.subrange(fraction_start as int, fraction_end as int);

        assert(decimal_is_wf_Sign(sign)) by {
            reveal(decimal_is_wf_Sign);
            if sign_end == sign_start {
                assert(sign.len() == 0);
            } else {
                assert(sign_start == 0);
                assert(sign_end == 1);
                assert(input@[0] as int == 45);
                assert(sign =~= seq!['\u{2d}']) by {
                    assert_seqs_equal!(sign == seq!['\u{2d}']);
                }
            }
            assert(exists|literal: Seq<char>|
                sign == literal
                    && (literal.len() == 0
                        || literal == seq!['\u{2d}'])) by {
                assert(
                    sign == sign
                        && (sign.len() == 0
                            || sign == seq!['\u{2d}'])
                );
            }
        }
        assert(decimal_is_wf_Natural(natural)) by {
            reveal(decimal_is_wf_Natural);
            assert(1 <= natural.len());
            assert forall|position: int| 0 <= position < natural.len() implies
                #[trigger] triptych_is_digit(natural[position]) by {
                assert(
                    natural[position]
                        == input@[natural_start as int + position]
                );
                assert(plan_token_accepts(
                    PlanTokenClass::Digit,
                    input@[natural_start as int + position],
                ));
                reveal(plan_token_accepts);
                reveal(triptych_is_digit);
            }
            assert(exists|digits: Seq<char>|
                natural == digits
                    && 1 <= digits.len()
                    && forall|position: int| #![auto]
                        0 <= position && position < digits.len()
                            ==> triptych_is_digit(digits[position])) by {
                assert(natural == natural);
            }
        }
        assert(decimal_is_wf_Fraction(fraction_digits)) by {
            reveal(decimal_is_wf_Fraction);
            assert(1 <= fraction_digits.len());
            assert(fraction_digits.len() <= 4);
            assert forall|position: int|
                0 <= position < fraction_digits.len() implies
                    #[trigger] triptych_is_digit(fraction_digits[position]) by {
                assert(
                    fraction_digits[position]
                        == input@[fraction_start as int + position]
                );
                assert(plan_token_accepts(
                    PlanTokenClass::Digit,
                    input@[fraction_start as int + position],
                ));
                reveal(plan_token_accepts);
                reveal(triptych_is_digit);
            }
            assert(exists|digits: Seq<char>|
                fraction_digits == digits
                    && 1 <= digits.len()
                    && digits.len() <= 4
                    && forall|position: int| #![auto]
                        0 <= position && position < digits.len()
                            ==> triptych_is_digit(digits[position])) by {
                assert(fraction_digits == fraction_digits);
            }
        }
        assert(
            input@
                =~= sign + natural + seq!['\u{2e}'] + fraction_digits
        ) by {
            assert_seqs_equal!(
                input@ == sign + natural + seq!['\u{2e}'] + fraction_digits
            );
        }
        assert(decimal_is_wf_Decimal(input@)) by {
            reveal(decimal_is_wf_Decimal);
        }
        let parsed_view = DecimalView {
            input: input@,
            sign,
            natural,
            fraction: fraction_digits,
        };
        assert(decimal_matches_view(input@, parsed_view)) by {
            reveal(decimal_matches_view);
        }
        assert(
            decimal_parse_view(
                input@,
                DecimalParseSpec {
                    end: input@.len() as int,
                    sign_start: sign_start as int,
                    sign_end: sign_end as int,
                    natural_start: natural_start as int,
                    natural_end: natural_end as int,
                    fraction_start: fraction_start as int,
                    fraction_end: fraction_end as int,
                },
            ) == parsed_view
        ) by {
            reveal(decimal_parse_view);
        }
        reveal(decimal_parse_plan);
        assert(fraction_exact == fraction as int);
    }

    Some(DecimalScanResult {
        end: fraction_end,
        sign_start,
        sign_end,
        natural_start,
        natural_end,
        fraction_start,
        fraction_end,
        natural,
        natural_overflow,
        fraction,
    })
}

impl DecimalParser {
    #[inline(always)]
    pub fn parse(input: &str) -> (result: Option<i64>)
        ensures
            match result {
                Some(value) =>
                    decimal_semantic_parse_plan(input@) == Some(value as int)
                        && decimal_is_valid(input@)
                        && exists|view: DecimalView|
                            decimal_matches_view(input@, view)
                                && decimal_view_valid(view)
                                && decimal_view_denotation(view)
                                    == value as int,
                None =>
                    decimal_semantic_parse_plan(input@).is_none()
                        && !decimal_is_valid(input@),
            },
    {
        let parsed = match decimal_scan(input) {
            Some(parsed) => parsed,
            None => {
                reveal(decimal_semantic_parse_plan);
                reveal(decimal_is_valid);
                reveal(decimal_is_wf);
                return None;
            },
        };
        let fraction = parsed.fraction;
        let fraction_length =
            parsed.fraction_end - parsed.fraction_start;
        let fraction_multiplier = if fraction_length == 1 {
            1000u64
        } else if fraction_length == 2 {
            100u64
        } else if fraction_length == 3 {
            10u64
        } else {
            1u64
        };
        assert(fraction_multiplier <= 1000);
        assert(fraction <= 9999);
        let scaled_fraction = fraction * fraction_multiplier;
        assert(scaled_fraction <= 9_999_000);
        if parsed.natural_overflow {
            proof {
                let view =
                    decimal_parse_view(input@, parsed.deep_view());
                let natural_value = triptych_nat_of(view.natural);
                let fraction_value = triptych_nat_of(view.fraction);
                assert(natural_value > DECIMAL_NATURAL_LIMIT);
                assert(fraction_value == fraction as int);
                assert(0 <= fraction_value);
                let negative = parsed.sign_start < parsed.sign_end;
                assert(decimal_matches_view(input@, view));
                assert(decimal_is_wf_Sign(view.sign)) by {
                    reveal(decimal_matches_view);
                }
                reveal(decimal_is_wf_Sign);
                let sign_literal = choose|literal: Seq<char>|
                    view.sign == literal
                        && (literal.len() == 0
                            || literal == seq!['\u{2d}']);
                assert(view.sign == sign_literal);
                if negative {
                    assert(0 < view.sign.len()) by {
                        reveal(decimal_parse_view);
                    }
                    assert(view.sign == seq!['\u{2d}']);
                    assert(triptych_sign_of(view.sign) == -1) by {
                        reveal(triptych_sign_of);
                    }
                } else {
                    assert(view.sign.len() == 0) by {
                        reveal(decimal_parse_view);
                    }
                    assert(triptych_sign_of(view.sign) == 1) by {
                        reveal(triptych_sign_of);
                    }
                }
                assert(1 <= fraction_length && fraction_length <= 4);
                assert(view.fraction.len() == fraction_length) by {
                    reveal(decimal_parse_view);
                }
                reveal_with_fuel(triptych_int_pow, 5);
                assert(triptych_int_pow(10, 4) == 10_000);
                if fraction_length == 1 {
                    assert(
                        triptych_int_pow(
                            10,
                            4 - view.fraction.len() as int,
                        ) == fraction_multiplier
                    );
                } else if fraction_length == 2 {
                    assert(
                        triptych_int_pow(
                            10,
                            4 - view.fraction.len() as int,
                        ) == fraction_multiplier
                    );
                } else if fraction_length == 3 {
                    assert(
                        triptych_int_pow(
                            10,
                            4 - view.fraction.len() as int,
                        ) == fraction_multiplier
                    );
                } else {
                    assert(fraction_length == 4);
                    assert(
                        triptych_int_pow(
                            10,
                            4 - view.fraction.len() as int,
                        ) == fraction_multiplier
                    );
                }
                reveal(decimal_semantic_parse_plan);
                reveal(decimal_view_valid);
                reveal(decimal_view_constraints);
                reveal(decimal_view_denotation);
                reveal(decimal_value);
                let total =
                    natural_value * 10_000
                        + fraction_value * fraction_multiplier;
                assert(
                    decimal_view_denotation(view)
                        == triptych_sign_of(view.sign)
                            * total
                );
                if negative {
                    assert(triptych_sign_of(view.sign) == -1);
                    lemma_mul_basics(total);
                    lemma_mul_unary_negation(1, total);
                    assert(
                        triptych_sign_of(view.sign) * total
                            == (-1int) * total
                    );
                    assert((-1int) * total == -total);
                    assert(
                        decimal_view_denotation(view) == -total
                    );
                } else {
                    assert(triptych_sign_of(view.sign) == 1);
                    lemma_mul_basics(total);
                    assert(
                        triptych_sign_of(view.sign) * total
                            == (1int) * total
                    );
                    assert((1int) * total == total);
                    assert(
                        decimal_view_denotation(view) == total
                    );
                }
                assert(
                    total > 9_223_372_036_854_775_808
                );
                assert(!decimal_view_valid(view));
                assert(decimal_semantic_parse_plan(input@).is_none());
                decimal_semantic_parse_plan_iff_valid(
                    input@,
                    parsed.deep_view(),
                );
                assert(!decimal_is_valid(input@));
            }
            return None;
        }
        let natural = parsed.natural;
        assert(natural <= DECIMAL_NATURAL_LIMIT);
        assert(
            natural * 10_000u64 + scaled_fraction
                <= 9_223_372_036_864_769_000u64
        );
        let magnitude = natural * 10_000u64 + scaled_fraction;
        let negative = parsed.sign_start < parsed.sign_end;
        proof {
            let view = decimal_parse_view(input@, parsed.deep_view());
            assert(decimal_matches_view(input@, view));
            assert(decimal_is_wf_Sign(view.sign)) by {
                reveal(decimal_matches_view);
            }
            reveal(decimal_is_wf_Sign);
            let sign_literal = choose|literal: Seq<char>|
                view.sign == literal
                    && (literal.len() == 0
                        || literal == seq!['\u{2d}']);
            assert(view.sign == sign_literal);
            if negative {
                assert(0 < view.sign.len()) by {
                    reveal(decimal_parse_view);
                }
                assert(view.sign == seq!['\u{2d}']);
                assert(triptych_sign_of(view.sign) == -1) by {
                    reveal(triptych_sign_of);
                }
            } else {
                assert(view.sign.len() == 0) by {
                    reveal(decimal_parse_view);
                }
                assert(triptych_sign_of(view.sign) == 1) by {
                    reveal(triptych_sign_of);
                }
            }
            assert(triptych_nat_of(view.natural) == natural as int);
            assert(triptych_nat_of(view.fraction) == fraction as int);
            assert(1 <= fraction_length && fraction_length <= 4);
            assert(view.fraction.len() == fraction_length) by {
                reveal(decimal_parse_view);
            }
            reveal_with_fuel(triptych_int_pow, 5);
            assert(triptych_int_pow(10, 4) == 10_000);
            if fraction_length == 1 {
                assert(
                    triptych_int_pow(
                        10,
                        4 - view.fraction.len() as int,
                    ) == fraction_multiplier
                );
            } else if fraction_length == 2 {
                assert(
                    triptych_int_pow(
                        10,
                        4 - view.fraction.len() as int,
                    ) == fraction_multiplier
                );
            } else if fraction_length == 3 {
                assert(
                    triptych_int_pow(
                        10,
                        4 - view.fraction.len() as int,
                    ) == fraction_multiplier
                );
            } else {
                assert(fraction_length == 4);
                assert(
                    triptych_int_pow(
                        10,
                        4 - view.fraction.len() as int,
                    ) == fraction_multiplier
                );
            }
            reveal(decimal_view_denotation);
            reveal(decimal_value);
            assert(
                decimal_view_denotation(view)
                    == triptych_sign_of(view.sign)
                        * (natural as int * 10_000
                            + fraction as int * fraction_multiplier as int)
            );
            assert(
                scaled_fraction as int
                    == fraction as int * fraction_multiplier as int
            );
            assert(
                magnitude as int
                    == natural as int * 10_000 + scaled_fraction as int
            );
            assert(
                decimal_view_denotation(view)
                    == if negative {
                        -(magnitude as int)
                    } else {
                        magnitude as int
                    }
            );
        }
        let limit = if negative {
            9_223_372_036_854_775_808u64
        } else {
            9_223_372_036_854_775_807u64
        };
        if limit < magnitude {
            proof {
                let view =
                    decimal_parse_view(input@, parsed.deep_view());
                reveal(decimal_semantic_parse_plan);
                reveal(decimal_view_valid);
                reveal(decimal_view_constraints);
                assert(!decimal_view_valid(view));
                assert(decimal_semantic_parse_plan(input@).is_none());
                decimal_semantic_parse_plan_iff_valid(
                    input@,
                    parsed.deep_view(),
                );
                assert(!decimal_is_valid(input@));
            }
            return None;
        }
        let value = if negative {
            if magnitude == 9_223_372_036_854_775_808u64 {
                i64::MIN
            } else {
                -(magnitude as i64)
            }
        } else {
            magnitude as i64
        };
        proof {
            let view = decimal_parse_view(input@, parsed.deep_view());
            reveal(decimal_semantic_parse_plan);
            reveal(decimal_view_valid);
            reveal(decimal_view_denotation);
            reveal(decimal_value);
            reveal(triptych_sign_of);
            reveal_with_fuel(triptych_int_pow, 5);
            assert(
                decimal_semantic_parse_plan(input@)
                    == Some(value as int)
            );
            reveal(decimal_is_valid);
            reveal(decimal_is_wf);
            reveal(decimal_satisfies_constraints);
            assert(decimal_is_valid(input@));
            assert(exists|matched: DecimalView|
                decimal_matches_view(input@, matched)
                    && decimal_view_valid(matched)
                    && decimal_view_denotation(matched) == value as int) by {
                assert(decimal_matches_view(input@, view));
                assert(decimal_view_valid(view));
                assert(decimal_view_denotation(view) == value as int);
            }
        }
        Some(value)
    }
}

} // verus!
