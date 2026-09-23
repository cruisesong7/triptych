# ! [allow (warnings)] use vest_lib::combinators::mapped::spec::* ;
use vest_lib::combinators::* ;
use vest_lib::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vest_lib::Never ;
use vest_lib::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vest_lib::core::exec::output::OutputBuf ;
use vest_lib::core::exec::parser::* ;
use vest_lib::core::exec::serializer::* ;
use vest_lib::core::exec::ParseError ;
use vest_lib::core::exec::bytes_eq ;
use vest_lib::core::{
    proof::*,
    spec::*
}
;
use vest_lib::primitives::btcvarint::VarInt ;
use vest_lib::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `digit`."]
pub type Digit = u8 ;
pub type DigitSpec = u8 ;


# [doc = "data type for `fraction`."]
pub type Fraction = [Digit ;
4] ;
pub type FractionSpec = Seq < DigitSpec > ;


# [doc = "data type for `decimal`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Decimal {
    pub natural: [Digit ;
    2],
    pub fraction: Fraction,
}
# [verifier::ext_equal]
pub struct DecimalSpec < T0 = Seq < DigitSpec >, T1 = FractionSpec > {
    pub natural: T0,
    pub fraction: T1,
}
pub type DecimalInner = (Seq < DigitSpec >, FractionSpec) ;
impl DeepView for Decimal {
    type V = DecimalSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        DecimalSpec {
            natural: self.natural.deep_view(),
            fraction: self.fraction.deep_view(),
        }
    }
}
impl Decimal {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().natural == self.natural.deep_view(),
    self.deep_view().fraction == self.fraction.deep_view(),
    {
        reveal(< Decimal as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > DecimalSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (natural,
        fraction) = input ;
        Self {
            natural,
            fraction
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            natural,
            fraction
        }
        = self ;
        (natural,
        fraction)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(DecimalSpec::from_structural) ;
        reveal(DecimalSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(DecimalSpec::from_structural) ;
        reveal(DecimalSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            natural,
            fraction
        }
        => (natural,
        fraction),
    }
   ,
    {
        reveal(DecimalSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DecimalForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DecimalReverse ;
impl SpecMap for DecimalForward {
    type Input = DecimalInner ;
    type Output = DecimalSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        DecimalSpec::from_structural (input)
    }
}
impl SpecMap for DecimalReverse {
    type Input = DecimalSpec ;
    type Output = DecimalInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `digit`."]
# [derive (Clone, Copy)]
pub struct DigitFmt ;

pub type DigitFmtSpec = Named < Refined < U8, PredFnSpec < u8 >> > ;

impl DigitFmt {
    # [doc = "specification constructor for `digit`."] pub open spec fn spec_inner() -> DigitFmtSpec {
        Named ("digit",
        Refined (U8,
        | x: u8 | x >= 48 && x <= 57))
    }
}


# [doc = "named format combinator for `fraction`."]
# [derive (Clone, Copy)]
pub struct FractionFmt ;

pub type FractionFmtSpec = Named < Array < 4, DigitFmt > > ;

impl FractionFmt {
    # [doc = "specification constructor for `fraction`."] pub open spec fn spec_inner() -> FractionFmtSpec {
        Named ("fraction",
        Array::< 4,
        _ > (DigitFmt))
    }
}


# [doc = "named format combinator for `decimal`."]
# [derive (Clone, Copy)]
pub struct DecimalFmt ;

pub type DecimalFmtSpec = Named < Mapped < Pair < Array < 2, DigitFmt >, PrefixTagged < U8, u8, FractionFmt > >, BiMap < DecimalForward, DecimalReverse >> > ;

impl DecimalFmt {
    # [doc = "specification constructor for `decimal`."] pub open spec fn spec_inner() -> DecimalFmtSpec {
        Named ("decimal",
        Mapped {
            inner: Pair (Array::< 2,
            _ > (DigitFmt),
            PrefixTagged (U8,
            46,
            FractionFmt)),
            mapper: BiMap (DecimalForward,
            DecimalReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for DigitFmt {
        type PVal = DigitSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for DigitFmt {
        type Val = DigitSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for DigitFmt {
        type SValue = DigitSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for DigitFmt {
        type SVal = DigitSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for DigitFmt {
        type T = DigitSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for FractionFmt {
        type PVal = FractionSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for FractionFmt {
        type Val = FractionSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for FractionFmt {
        type SValue = FractionSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for FractionFmt {
        type SVal = FractionSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for FractionFmt {
        type T = FractionSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for DecimalFmt {
        type PVal = DecimalSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for DecimalFmt {
        type Val = DecimalSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for DecimalFmt {
        type SValue = DecimalSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for DecimalFmt {
        type SVal = DecimalSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for DecimalFmt {
        type T = DecimalSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }
}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;
    broadcast use {
        vest_lib::combinators::disjoint::disjointness_lemmas,
        DecimalSpec::lemma_from_into,
        DecimalSpec::lemma_into_from,
    };

    impl SafeParser for DigitFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< DigitFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for DigitFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< DigitFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for DigitFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< DigitFmt as SpecParser>::spec_parse) ;
            reveal(< DigitFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< DigitFmt as SpecParser>::spec_parse) ;
            reveal(< DigitFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for DigitFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DigitFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DigitFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DigitFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for DigitFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< DigitFmt as SpecSerializer>::spec_serialize) ;
            reveal(< DigitFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for DigitFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< DigitFmt as SpecParser>::spec_parse) ;
            reveal(< DigitFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DigitFmt as Consistency>::consistent) ;
            reveal(< DigitFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for DigitFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< DigitFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for DigitFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< DigitFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DigitFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for DigitFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< DigitFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DigitFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for FractionFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for FractionFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< FractionFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for FractionFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecParser>::spec_parse) ;
            reveal(< FractionFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecParser>::spec_parse) ;
            reveal(< FractionFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for FractionFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for FractionFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< FractionFmt as SpecSerializer>::spec_serialize) ;
            reveal(< FractionFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for FractionFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecParser>::spec_parse) ;
            reveal(< FractionFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFmt as Consistency>::consistent) ;
            reveal(< FractionFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for FractionFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< FractionFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for FractionFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for FractionFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< FractionFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for DecimalFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< DecimalFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for DecimalFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< DecimalFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for DecimalFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< DecimalFmt as SpecParser>::spec_parse) ;
            reveal(< DecimalFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: DecimalInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                DecimalSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< DecimalFmt as SpecParser>::spec_parse) ;
            reveal(< DecimalFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: DecimalInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                DecimalSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for DecimalFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DecimalFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< DecimalFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DecimalFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for DecimalFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< DecimalFmt as SpecSerializer>::spec_serialize) ;
            reveal(< DecimalFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for DecimalFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< DecimalFmt as SpecParser>::spec_parse) ;
            reveal(< DecimalFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DecimalFmt as Consistency>::consistent) ;
            reveal(< DecimalFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: DecimalSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                DecimalSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for DecimalFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< DecimalFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: DecimalInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                DecimalSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for DecimalFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< DecimalFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DecimalFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for DecimalFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< DecimalFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< DecimalFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }
}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for DigitFmt {
        type PT = Digit;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<DigitFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(ibuf)?;
            if !(v >= 48 && v <= 57) {
                return Err(ParseError::predicate_failed());
            }
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Digit> for DigitFmt {
        fn serialize_into(&self, v: &Digit, obuf: &mut Output) {
            reveal(<DigitFmt as SpecSerializer>::spec_serialize);
            reveal(<DigitFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            U8.serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Digit> for DigitFmt {
        fn prepare(&self, v: &Digit) -> Result<usize, PreSerializeError> {
            reveal(<DigitFmt as SpecByteLen>::byte_len);
            {
        if ! (*v >= 48 && *v <= 57) {
            Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
        }
        else {
            (U8).prepare (v)
        }
    }
        }
    }



    impl<'i> Parser<&'i [u8]> for FractionFmt {
        type PT = Fraction;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FractionFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Array::< 4, _ > (DigitFmt).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Fraction> for FractionFmt {
        fn serialize_into(&self, v: &Fraction, obuf: &mut Output) {
            reveal(<FractionFmt as SpecSerializer>::spec_serialize);
            reveal(<FractionFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Array::< 4, _ > (DigitFmt).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Fraction> for FractionFmt {
        fn prepare(&self, v: &Fraction) -> Result<usize, PreSerializeError> {
            reveal(<FractionFmt as SpecByteLen>::byte_len);
            (Array::< 4, _ > (DigitFmt)).prepare (v)
        }
    }



    impl<'i> Parser<&'i [u8]> for DecimalFmt {
        type PT = Decimal;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DecimalFmt as SpecParser>::spec_parse);
            reveal(<Decimal as DeepView>::deep_view);
            reveal(DecimalSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, natural) = (Array::< 2, _ > (DigitFmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, fraction) = (PrefixTagged (U8, 46, FractionFmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Decimal {
                natural,
                fraction,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Decimal> for DecimalFmt {
        fn serialize_into(&self, v: &Decimal, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DecimalFmt as SpecSerializer>::spec_serialize);
            reveal(<DecimalFmt as SpecByteLen>::byte_len);
            reveal(<Decimal as DeepView>::deep_view);
            reveal(DecimalSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Decimal {
                natural,
                fraction,
            } = v;
            Array::< 2, _ > (DigitFmt).serialize_into(natural, obuf);
            PrefixTagged (U8, 46, FractionFmt).serialize_into(fraction, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Decimal> for DecimalFmt {
        fn prepare(&self, v: &Decimal) -> Result<usize, PreSerializeError> {
            reveal(<DecimalFmt as SpecByteLen>::byte_len);
            reveal(<Decimal as DeepView>::deep_view);
            reveal(DecimalSpec::into_structural);
            let Decimal {
                natural,
                fraction,
            } = v;
            let l1 = (Array::< 2, _ > (DigitFmt)).prepare (natural) ?;
            let l2 = (PrefixTagged (U8, 46, FractionFmt)).prepare (fraction) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
