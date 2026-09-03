use cedar_policy::{
    eval_expression, Context, Entities, EntityUid, EvalResult, Expression, Request,
};
use std::str::FromStr;

fn request() -> Request {
    Request::new(
        EntityUid::from_str(r#"User::"alice""#).expect("valid principal"),
        EntityUid::from_str(r#"Action::"test""#).expect("valid action"),
        EntityUid::from_str(r#"Resource::"document""#).expect("valid resource"),
        Context::empty(),
        None,
    )
    .expect("valid request")
}

fn evaluate(expression: &Expression) -> Result<EvalResult, String> {
    eval_expression(&request(), &Entities::empty(), expression).map_err(|error| error.to_string())
}

fn cedar_decimal(input: &str) -> Result<(), String> {
    match evaluate(&Expression::new_decimal(input))? {
        EvalResult::ExtensionValue(_) => Ok(()),
        other => Err(format!("decimal constructor returned {other:?}")),
    }
}

fn cedar_decimal_equals(left: &str, right: &str) -> Result<bool, String> {
    let source = format!("decimal({left:?}) == decimal({right:?})");
    let expression = Expression::from_str(&source).map_err(|error| error.to_string())?;
    match evaluate(&expression)? {
        EvalResult::Bool(equal) => Ok(equal),
        other => Err(format!("decimal equality returned {other:?}")),
    }
}

// These are the valid inputs exercised by
// cedar-policy-core/src/extensions/decimal.rs::tests::decimal_creation.
const VALID_CASES: &[(&str, &str)] = &[
    ("1.0", "1.0000"),
    ("-1.0", "-1.0000"),
    ("123.456", "123.4560"),
    ("0.1234", "0.1234"),
    ("-0.0123", "-0.0123"),
    ("55.1", "55.1000"),
    ("-922337203685477.5808", "-922337203685477.5808"),
    ("00.000", "0.0000"),
];

// These are the invalid inputs exercised by the same Cedar unit test.
const INVALID_CASES: &[&str] = &[
    "1234",
    "1.0.",
    "1.",
    ".1",
    "1.a",
    "-.",
    "1000000000000000.0",
    "922337203685477.5808",
    "-922337203685477.5809",
    "-922337203685478.0",
    "0.12345",
    "0.00000",
];

#[test]
fn production_parser_matches_cedar_valid_corpus() {
    for (input, expected) in VALID_CASES {
        assert!(
            cedar_decimal(input).is_ok(),
            "Cedar unexpectedly rejected {input:?}"
        );
        assert_eq!(
            cedar_decimal_equals(input, expected),
            Ok(true),
            "Cedar returned the wrong Decimal value for {input:?}"
        );
    }
}

#[test]
fn production_parser_matches_cedar_invalid_corpus() {
    for input in INVALID_CASES {
        assert!(
            cedar_decimal(input).is_err(),
            "Cedar unexpectedly accepted {input:?}"
        );
    }
}
