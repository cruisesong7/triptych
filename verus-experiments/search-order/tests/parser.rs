use triptych_search_order::parser::{search_order_parse_candidate, CaptureKey};

/// Production indices follow grammar order: Root = 0, Any = 1, Pair = 2.
fn captured_productions(input: &str) -> Option<Vec<usize>> {
    search_order_parse_candidate(input).map(|candidate| {
        candidate
            .captures
            .iter()
            .filter_map(|capture| match capture.key {
                CaptureKey::Production(production) => Some(production),
                _ => None,
            })
            .collect()
    })
}

#[test]
fn ordered_choice_selects_first_complete_alternative() {
    // `Pair` also accepts "ab", but source order selects `Any`, as the Lean scanner does.
    assert_eq!(captured_productions("ab"), Some(vec![1]));
    assert_eq!(captured_productions("ba"), Some(vec![1]));
    assert_eq!(captured_productions("c"), None);
}
