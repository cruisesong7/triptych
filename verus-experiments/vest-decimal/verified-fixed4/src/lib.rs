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
    fn parser_and_serializer_roundtrip() {
        let input = b"12.3400";
        let value = parse_all(input).expect("fixed-four Decimal should parse");
        assert_eq!(value.natural, [b'1', b'2']);
        assert_eq!(value.fraction, [b'3', b'4', b'0', b'0']);

        let length = DecimalFmt.prepare(&value).expect("parsed value should prepare");
        let mut output = vec![0; length];
        DecimalFmt.serialize(&value, &mut output);
        assert_eq!(output, input);
    }

    #[test]
    fn rejects_invalid_shape() {
        assert!(parse_all(b"12.34").is_none());
        assert!(parse_all(b"1.3400").is_none());
        assert!(parse_all(b"-12.3400").is_none());
        assert!(parse_all(b"+12.3400").is_none());
        assert!(parse_all(b"12.34a0").is_none());
    }
}
