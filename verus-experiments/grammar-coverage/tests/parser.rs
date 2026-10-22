use triptych_grammar_coverage::parser::grammar_coverage_parse_candidate;

#[test]
fn accepts_each_supported_constructor() {
    for input in [
        "123",
        "λ1,2,A",
        "λ\"quoted\"1,2,A",
        "AZ",
        "0:1;1:0",
        "0,1,0,1,1",
    ] {
        assert!(
            grammar_coverage_parse_candidate(input).is_some(),
            "input {input:?}"
        );
    }
}

#[test]
fn rejects_incomplete_inputs() {
    for input in ["", "λ", "λ1,", "λG", "A", "0:", "0:1;", "0,"] {
        assert!(
            grammar_coverage_parse_candidate(input).is_none(),
            "input {input:?}"
        );
    }
}
