// Proof that the handwritten parser implements Triptych's generated contract.

use crate::contract::DecimalExternalParserContract;
#[cfg(verus_only)]
use crate::contract::{decimal_has_result, decimal_matches_result};
use crate::optimized::DecimalParser;
#[cfg(verus_only)]
use crate::parser::{
    decimal_matches_view_parse_plan, decimal_parse_plan, decimal_parse_view,
    decimal_semantic_parse_plan, plan_scan_token_end, plan_token_accepts, DecimalParseSpec,
    PlanTokenClass,
};
#[cfg(verus_only)]
use crate::printer::{
    decimal_canonical_characters, decimal_extparse_normalize_eq_iff_parse_eq,
    decimal_extparse_to_string_injective, decimal_extparse_to_string_roundtrip,
};
use crate::spec::*;
#[cfg(verus_only)]
use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

/** The executable parser's generated semantic result. */
pub open spec fn decimal_external_parse_to_spec(input: Seq<char>) -> Option<int>
{
    decimal_semantic_parse_plan(input)
}

pub proof fn decimal_matches_result_implies_valid(input: Seq<char>, value: int)
    requires
        decimal_matches_result(input, value),
    ensures
        decimal_is_valid(input),
{
    reveal(decimal_matches_result);
    let view = choose|view: DecimalView|
        decimal_matches_view(input, view)
            && decimal_view_valid(view)
            && decimal_view_denotation(view) == value;
    reveal(decimal_view_valid);
    reveal(decimal_is_valid);
    reveal(decimal_is_wf);
    reveal(decimal_satisfies_constraints);
    reveal(decimal_matches_view);
    reveal(decimal_is_wf_Decimal);
    assert(decimal_is_wf_Decimal(input));
    assert(exists|matched: DecimalView|
        decimal_matches_view(input, matched)
            && decimal_view_constraints(matched)) by {
        assert(decimal_matches_view(input, view));
        assert(decimal_view_constraints(view));
    }
}

pub proof fn decimal_valid_has_result(input: Seq<char>)
    requires
        decimal_is_valid(input),
    ensures
        exists|value: int| decimal_matches_result(input, value),
{
    reveal(decimal_is_valid);
    reveal(decimal_satisfies_constraints);
    let view = choose|view: DecimalView|
        decimal_matches_view(input, view)
            && decimal_view_constraints(view);
    let value = decimal_view_denotation(view);
    reveal(decimal_matches_result);
    reveal(decimal_view_valid);
    assert(decimal_matches_result(input, value)) by {
        assert(decimal_matches_view(input, view));
        assert(decimal_view_valid(view));
        assert(decimal_view_denotation(view) == value);
    }
}

pub proof fn decimal_has_result_bounds(value: int)
    requires
        decimal_has_result(value),
    ensures
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
{
    reveal(decimal_has_result);
    let input = choose|input: Seq<char>| decimal_matches_result(input, value);
    reveal(decimal_matches_result);
    let view = choose|view: DecimalView|
        decimal_matches_view(input, view)
            && decimal_view_valid(view)
            && decimal_view_denotation(view) == value;
    reveal(decimal_view_valid);
    reveal(decimal_view_constraints);
    reveal(decimal_constraints);
    reveal(decimal_view_denotation);
}

pub proof fn decimal_matches_result_unique(
    input: Seq<char>,
    left: int,
    right: int,
)
    requires
        decimal_matches_result(input, left),
        decimal_matches_result(input, right),
    ensures
        left == right,
{
    reveal(decimal_matches_result);
    let left_view = choose|view: DecimalView|
        decimal_matches_view(input, view)
            && decimal_view_valid(view)
            && decimal_view_denotation(view) == left;
    let right_view = choose|view: DecimalView|
        decimal_matches_view(input, view)
            && decimal_view_valid(view)
            && decimal_view_denotation(view) == right;
    decimal_matches_view_parse_plan(input, left_view);
    decimal_matches_view_parse_plan(input, right_view);
    match decimal_parse_plan(input) {
        Some(parsed) => {
            assert(left_view.sign
                == input.subrange(parsed.sign_start, parsed.sign_end));
            assert(right_view.sign
                == input.subrange(parsed.sign_start, parsed.sign_end));
            assert(left_view.natural
                == input.subrange(parsed.natural_start, parsed.natural_end));
            assert(right_view.natural
                == input.subrange(parsed.natural_start, parsed.natural_end));
            assert(left_view.fraction
                == input.subrange(parsed.fraction_start, parsed.fraction_end));
            assert(right_view.fraction
                == input.subrange(parsed.fraction_start, parsed.fraction_end));
            reveal(decimal_view_denotation);
            reveal(decimal_value);
        },
        None => {
            assert(false);
        },
    }
}

pub proof fn decimal_plan_scan_accepts(
    input: Seq<char>,
    start: int,
    limit: int,
    token: PlanTokenClass,
)
    requires
        0 <= start <= limit <= input.len(),
    ensures
        start <= plan_scan_token_end(input, start, limit, token) <= limit,
        forall|position: int|
            start <= position
                < plan_scan_token_end(input, start, limit, token) ==>
                #[trigger] plan_token_accepts(token, input[position]),
    decreases limit - start,
{
    if start < limit && plan_token_accepts(token, input[start]) {
        decimal_plan_scan_accepts(input, start + 1, limit, token);
        reveal(plan_scan_token_end);
    } else {
        reveal(plan_scan_token_end);
    }
}

pub proof fn decimal_parse_plan_matches_generated_view(
    input: Seq<char>,
    parsed: DecimalParseSpec,
)
    requires
        decimal_parse_plan(input) == Some(parsed),
    ensures
        decimal_is_wf_Decimal(input),
        decimal_matches_view(
            input,
            decimal_parse_view(input, parsed),
        ),
{
    reveal(decimal_parse_plan);
    let sign_start = 0int;
    let sign_end =
        if input.len() > 0 && input[0] as int == 45 {
            1int
        } else {
            0int
        };
    let natural_start = sign_end;
    let natural_end = plan_scan_token_end(
        input,
        natural_start,
        input.len() as int,
        PlanTokenClass::Digit,
    );
    let fraction_start = natural_end + 1;
    let fraction_end = plan_scan_token_end(
        input,
        fraction_start,
        input.len() as int,
        PlanTokenClass::Digit,
    );
    assert(
        parsed == DecimalParseSpec {
            end: fraction_end,
            sign_start,
            sign_end,
            natural_start,
            natural_end,
            fraction_start,
            fraction_end,
        }
    );
    decimal_plan_scan_accepts(
        input,
        natural_start,
        input.len() as int,
        PlanTokenClass::Digit,
    );
    decimal_plan_scan_accepts(
        input,
        fraction_start,
        input.len() as int,
        PlanTokenClass::Digit,
    );

    let sign = input.subrange(sign_start, sign_end);
    let natural = input.subrange(natural_start, natural_end);
    let fraction = input.subrange(fraction_start, fraction_end);
    assert(decimal_is_wf_Sign(sign)) by {
        reveal(decimal_is_wf_Sign);
        if sign_end == 0 {
            assert(sign.len() == 0);
        } else {
            assert(sign_end == 1);
            assert(input[0] as int == 45);
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
            let source = natural_start + position;
            assert(natural[position] == input[source]);
            assert(plan_token_accepts(
                PlanTokenClass::Digit,
                input[source],
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
    assert(decimal_is_wf_Fraction(fraction)) by {
        reveal(decimal_is_wf_Fraction);
        assert(1 <= fraction.len());
        assert(fraction.len() <= 4);
        assert forall|position: int| 0 <= position < fraction.len() implies
            #[trigger] triptych_is_digit(fraction[position]) by {
            let source = fraction_start + position;
            assert(fraction[position] == input[source]);
            assert(plan_token_accepts(
                PlanTokenClass::Digit,
                input[source],
            ));
            reveal(plan_token_accepts);
            reveal(triptych_is_digit);
        }
        assert(exists|digits: Seq<char>|
            fraction == digits
                && 1 <= digits.len()
                && digits.len() <= 4
                && forall|position: int| #![auto]
                    0 <= position && position < digits.len()
                        ==> triptych_is_digit(digits[position])) by {
            assert(fraction == fraction);
        }
    }
    assert(input[natural_end] == '\u{2e}');
    assert(fraction_end == input.len());
    assert(input =~= sign + natural + seq!['\u{2e}'] + fraction) by {
        assert_seqs_equal!(
            input == sign + natural + seq!['\u{2e}'] + fraction
        );
    }
    assert(decimal_is_wf_Decimal(input)) by {
        reveal(decimal_is_wf_Decimal);
    }
    let view = DecimalView {
        input,
        sign,
        natural,
        fraction,
    };
    assert(decimal_matches_view(input, view)) by {
        reveal(decimal_matches_view);
    }
    assert(decimal_parse_view(input, parsed) == view) by {
        reveal(decimal_parse_view);
    }
}

pub proof fn decimal_external_parse_sound(input: Seq<char>, value: int)
    requires
        match decimal_external_parse_to_spec(input) {
            Some(parsed) => parsed == value,
            None => false,
        },
    ensures
        decimal_is_valid(input),
        decimal_matches_result(input, value),
{
    reveal(decimal_external_parse_to_spec);
    reveal(decimal_semantic_parse_plan);
    match decimal_parse_plan(input) {
        Some(parsed) => {
            let view = decimal_parse_view(input, parsed);
            decimal_parse_plan_matches_generated_view(input, parsed);
            assert(decimal_view_valid(view));
            assert(decimal_view_denotation(view) == value);
            assert(decimal_matches_result(input, value)) by {
                reveal(decimal_matches_result);
            }
            decimal_matches_result_implies_valid(input, value);
        },
        None => {
            assert(false);
        },
    }
}

pub proof fn decimal_external_parse_complete(input: Seq<char>, value: int)
    requires
        decimal_is_valid(input),
        decimal_matches_result(input, value),
    ensures
        match decimal_external_parse_to_spec(input) {
            Some(parsed) => parsed == value,
            None => false,
        },
{
    reveal(decimal_matches_result);
    let view = choose|view: DecimalView|
        decimal_matches_view(input, view)
            && decimal_view_valid(view)
            && decimal_view_denotation(view) == value;
    decimal_matches_view_parse_plan(input, view);
    let parsed = match decimal_parse_plan(input) {
        Some(parsed) => parsed,
        None => {
            assert(false);
            arbitrary()
        },
    };
    let canonical = decimal_parse_view(input, parsed);
    assert(canonical.input == view.input) by {
        reveal(decimal_matches_view);
        reveal(decimal_parse_view);
    }
    assert(canonical.sign == view.sign);
    assert(canonical.natural == view.natural);
    assert(canonical.fraction == view.fraction);
    assert(decimal_view_valid(canonical)) by {
        reveal(decimal_view_valid);
        reveal(decimal_view_constraints);
        reveal(decimal_constraints);
        reveal(decimal_value);
    }
    assert(decimal_view_denotation(canonical) == value) by {
        reveal(decimal_view_denotation);
        reveal(decimal_value);
    }
    reveal(decimal_external_parse_to_spec);
    reveal(decimal_semantic_parse_plan);
}

pub proof fn decimal_external_parse_reject(input: Seq<char>)
    ensures
        (match decimal_external_parse_to_spec(input) {
            Some(parsed) => false,
            None => true,
        }) ==> !decimal_is_valid(input),
        !decimal_is_valid(input) ==> (match decimal_external_parse_to_spec(input) {
            Some(parsed) => false,
            None => true,
        }),
{
    if decimal_external_parse_to_spec(input).is_none() {
        if decimal_is_valid(input) {
            decimal_valid_has_result(input);
            let value = choose|value: int|
                decimal_matches_result(input, value);
            decimal_external_parse_complete(input, value);
            assert(false);
        }
    }
    if !decimal_is_valid(input) {
        match decimal_external_parse_to_spec(input) {
            Some(value) => {
                decimal_external_parse_sound(input, value);
                assert(false);
            },
            None => {},
        }
    }
}

impl DecimalExternalParserContract for DecimalParser {
    open spec fn parse_to_spec(input: Seq<char>) -> Option<int> {
        decimal_external_parse_to_spec(input)
    }

    proof fn extparse_sound(input: Seq<char>, value: int) {
        decimal_external_parse_sound(input, value);
    }

    proof fn extparse_complete(input: Seq<char>, value: int) {
        decimal_external_parse_complete(input, value);
    }

    proof fn extparse_reject(input: Seq<char>) {
        decimal_external_parse_reject(input);
    }

    open spec fn to_string_to_spec(value: int) -> Seq<char> {
        decimal_canonical_characters(value)
    }

    proof fn extparse_to_string_roundtrip(value: int) {
        decimal_extparse_to_string_roundtrip(value);
    }

    proof fn extparse_to_string_injective(left: int, right: int) {
        decimal_extparse_to_string_injective(left, right);
    }

    proof fn extparse_normalize_eq_iff_parse_eq(left: Seq<char>, right: Seq<char>) {
        decimal_extparse_normalize_eq_iff_parse_eq(left, right);
    }
}

} // verus!
