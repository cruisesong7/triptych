pub mod decimal;

#[cfg(test)]
mod tests {
    use super::decimal::*;
    use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

    fn parse_all(input: &[u8]) -> Option<Decimal> {
        let (consumed, value) = DecimalFmt.parse(&input).ok()?;
        (consumed == input.len()).then_some(value)
    }

    #[test]
    fn parses_triptych_decimal_examples() {
        let negative = parse_all(b"-12.34").expect("negative Decimal should parse");
        assert_eq!(negative.sign, Some(()));
        assert_eq!(negative.natural_first, b'1');
        assert_eq!(negative.natural_following_digits, vec![b'2']);
        assert!(matches!(negative.fraction, Fraction::Two([b'3', b'4'])));

        assert!(parse_all(b"0.0").is_some());
        assert!(parse_all(b"001.2345").is_some());
    }

    #[test]
    fn rejects_outside_triptych_decimal_grammar() {
        assert!(parse_all(b"12.").is_none());
        assert!(parse_all(b".12").is_none());
        assert!(parse_all(b"+12.34").is_none());
        assert!(parse_all(b"12.34567").is_none());
        assert!(parse_all(b"12.a").is_none());
    }

    #[test]
    fn serializer_roundtrips_parser_output() {
        let input = b"-12.34";
        let value = parse_all(input).expect("Decimal should parse");
        let length = DecimalFmt.prepare(&value).expect("parsed value should prepare");
        let mut output = vec![0; length];
        DecimalFmt.serialize(&value, &mut output);
        assert_eq!(output, input);
    }
}
