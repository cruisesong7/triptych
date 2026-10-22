use triptych_direct_coverage::parser::direct_coverage_parse_candidate;

#[test]
fn accepts_straight_line_shapes() {
    for input in ["12-Af:101/UP", "+7-0:1/AZ", "999-ABCD:0011/XY"] {
        assert!(
            direct_coverage_parse_candidate(input).is_some(),
            "input {input:?}"
        );
    }
}

#[test]
fn rejects_bad_boundaries_and_token_classes() {
    for input in [
        "",
        "+",
        "12:Af:101/UP",
        "12-G:101/UP",
        "12-Af:102/UP",
        "12-Af:101/Up",
        "12-ABCDE:1/AZ",
    ] {
        assert!(
            direct_coverage_parse_candidate(input).is_none(),
            "input {input:?}"
        );
    }
}
