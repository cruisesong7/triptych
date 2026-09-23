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


# [doc = "data type for `fraction_one`."]
pub type FractionOne = [Digit ;
1] ;
pub type FractionOneSpec = Seq < DigitSpec > ;


# [doc = "data type for `fraction_two`."]
pub type FractionTwo = [Digit ;
2] ;
pub type FractionTwoSpec = Seq < DigitSpec > ;


# [doc = "data type for `fraction_three`."]
pub type FractionThree = [Digit ;
3] ;
pub type FractionThreeSpec = Seq < DigitSpec > ;


# [doc = "data type for `fraction_four`."]
pub type FractionFour = [Digit ;
4] ;
pub type FractionFourSpec = Seq < DigitSpec > ;


# [doc = "data type for `fraction`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Fraction {
    One (FractionOne),
    Two (FractionTwo),
    Three (FractionThree),
    Four (FractionFour),
}
# [verifier::ext_equal]
pub enum FractionSpec < T0 = FractionOneSpec, T1 = FractionTwoSpec, T2 = FractionThreeSpec, T3 = FractionFourSpec > {
    One (T0),
    Two (T1),
    Three (T2),
    Four (T3),
}
pub type FractionInner = Sum < Sum < FractionOneSpec, FractionTwoSpec >, Sum < FractionThreeSpec, FractionFourSpec > > ;
impl DeepView for Fraction {
    type V = FractionSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            Fraction::One (v) => FractionSpec::One (v.deep_view()),
            Fraction::Two (v) => FractionSpec::Two (v.deep_view()),
            Fraction::Three (v) => FractionSpec::Three (v.deep_view()),
            Fraction::Four (v) => FractionSpec::Four (v.deep_view()),
        }
    }
}
impl Fraction {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        Fraction::One (v) => FractionSpec::One (v.deep_view()),
        Fraction::Two (v) => FractionSpec::Two (v.deep_view()),
        Fraction::Three (v) => FractionSpec::Three (v.deep_view()),
        Fraction::Four (v) => FractionSpec::Four (v.deep_view()),
    }
   ,
    {
        reveal(< Fraction as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3 > FractionSpec < T0, T1, T2, T3 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >) -> Self {
        match input {
            L (L (value)) => Self::One (value),
            L (R (value)) => Self::Two (value),
            R (L (value)) => Self::Three (value),
            R (R (value)) => Self::Four (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > > {
        match self {
            Self::One (value) => L (L (value)),
            Self::Two (value) => L (R (value)),
            Self::Three (value) => R (L (value)),
            Self::Four (value) => R (R (value)),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(FractionSpec::from_structural) ;
        reveal(FractionSpec::into_structural) ;
        match self {
            Self::One (_) => {
            }
           ,
            Self::Two (_) => {
            }
           ,
            Self::Three (_) => {
            }
           ,
            Self::Four (_) => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(FractionSpec::from_structural) ;
        reveal(FractionSpec::into_structural) ;
        match input {
            L (L (_)) => {
            }
           ,
            L (R (_)) => {
            }
           ,
            R (L (_)) => {
            }
           ,
            R (R (_)) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::One (value) => L (L (value)),
        Self::Two (value) => L (R (value)),
        Self::Three (value) => R (L (value)),
        Self::Four (value) => R (R (value)),
    }
   ,
    {
        reveal(FractionSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FractionForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FractionReverse ;
impl SpecMap for FractionForward {
    type Input = FractionInner ;
    type Output = FractionSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        FractionSpec::from_structural (input)
    }
}
impl SpecMap for FractionReverse {
    type Input = FractionSpec ;
    type Output = FractionInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `decimal`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct Decimal {
    pub sign: Option <() >,
    pub natural_first: Digit,
    pub natural_following_digits: Vec < Digit >,
    pub fraction: Fraction,
}
# [verifier::ext_equal]
pub struct DecimalSpec < T0 = Option <() >, T1 = DigitSpec, T2 = Seq < DigitSpec >, T3 = FractionSpec > {
    pub sign: T0,
    pub natural_first: T1,
    pub natural_following_digits: T2,
    pub fraction: T3,
}
pub type DecimalInner = (Option <() >, (DigitSpec, (Seq < DigitSpec >, FractionSpec))) ;
impl DeepView for Decimal {
    type V = DecimalSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        DecimalSpec {
            sign: self.sign.deep_view(),
            natural_first: self.natural_first.deep_view(),
            natural_following_digits: self.natural_following_digits.deep_view(),
            fraction: self.fraction.deep_view(),
        }
    }
}
impl Decimal {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().sign == self.sign.deep_view(),
    self.deep_view().natural_first == self.natural_first.deep_view(),
    self.deep_view().natural_following_digits == self.natural_following_digits.deep_view(),
    self.deep_view().fraction == self.fraction.deep_view(),
    {
        reveal(< Decimal as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3 > DecimalSpec < T0, T1, T2, T3 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    (T2,
    T3)))) -> Self {
        let (sign,
        (natural_first,
        (natural_following_digits,
        fraction))) = input ;
        Self {
            sign,
            natural_first,
            natural_following_digits,
            fraction
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    (T2,
    T3))) {
        let Self {
            sign,
            natural_first,
            natural_following_digits,
            fraction
        }
        = self ;
        (sign,
        (natural_first,
        (natural_following_digits,
        fraction)))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(DecimalSpec::from_structural) ;
        reveal(DecimalSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    (T2,
    T3)))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(DecimalSpec::from_structural) ;
        reveal(DecimalSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            sign,
            natural_first,
            natural_following_digits,
            fraction
        }
        => (sign,
        (natural_first,
        (natural_following_digits,
        fraction))),
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


# [doc = "named format combinator for `fraction_one`."]
# [derive (Clone, Copy)]
pub struct FractionOneFmt ;

pub type FractionOneFmtSpec = Named < AndThen < Tail, Array < 1, DigitFmt > > > ;

impl FractionOneFmt {
    # [doc = "specification constructor for `fraction_one`."] pub open spec fn spec_inner() -> FractionOneFmtSpec {
        Named ("fraction_one",
        AndThen (Tail,
        Array::< 1,
        _ > (DigitFmt)))
    }
}


# [doc = "named format combinator for `fraction_two`."]
# [derive (Clone, Copy)]
pub struct FractionTwoFmt ;

pub type FractionTwoFmtSpec = Named < AndThen < Tail, Array < 2, DigitFmt > > > ;

impl FractionTwoFmt {
    # [doc = "specification constructor for `fraction_two`."] pub open spec fn spec_inner() -> FractionTwoFmtSpec {
        Named ("fraction_two",
        AndThen (Tail,
        Array::< 2,
        _ > (DigitFmt)))
    }
}


# [doc = "named format combinator for `fraction_three`."]
# [derive (Clone, Copy)]
pub struct FractionThreeFmt ;

pub type FractionThreeFmtSpec = Named < AndThen < Tail, Array < 3, DigitFmt > > > ;

impl FractionThreeFmt {
    # [doc = "specification constructor for `fraction_three`."] pub open spec fn spec_inner() -> FractionThreeFmtSpec {
        Named ("fraction_three",
        AndThen (Tail,
        Array::< 3,
        _ > (DigitFmt)))
    }
}


# [doc = "named format combinator for `fraction_four`."]
# [derive (Clone, Copy)]
pub struct FractionFourFmt ;

pub type FractionFourFmtSpec = Named < AndThen < Tail, Array < 4, DigitFmt > > > ;

impl FractionFourFmt {
    # [doc = "specification constructor for `fraction_four`."] pub open spec fn spec_inner() -> FractionFourFmtSpec {
        Named ("fraction_four",
        AndThen (Tail,
        Array::< 4,
        _ > (DigitFmt)))
    }
}


# [doc = "named format combinator for `fraction`."]
# [derive (Clone, Copy)]
pub struct FractionFmt ;

pub type FractionFmtSpec = Named < Mapped < Choice < Choice < FractionOneFmt, FractionTwoFmt >, Choice < FractionThreeFmt, FractionFourFmt > >, BiMap < FractionForward, FractionReverse >> > ;

impl FractionFmt {
    # [doc = "specification constructor for `fraction`."] pub open spec fn spec_inner() -> FractionFmtSpec {
        Named ("fraction",
        Mapped {
            inner: Choice (Choice (FractionOneFmt,
            FractionTwoFmt),
            Choice (FractionThreeFmt,
            FractionFourFmt)),
            mapper: BiMap (FractionForward,
            FractionReverse),
        }
        )
    }
}


# [doc = "named format combinator for `decimal`."]
# [derive (Clone, Copy)]
pub struct DecimalFmt ;

pub type DecimalFmtSpec = Named < Mapped < Optional < PrefixTagged < U8, u8, Empty >, Pair < DigitFmt, Repeat < DigitFmt, PrefixTagged < U8, u8, FractionFmt > > > >, BiMap < DecimalForward, DecimalReverse >> > ;

impl DecimalFmt {
    # [doc = "specification constructor for `decimal`."] pub open spec fn spec_inner() -> DecimalFmtSpec {
        Named ("decimal",
        Mapped {
            inner: Optional (PrefixTagged (U8,
            45,
            Empty),
            Pair (DigitFmt,
            Repeat (DigitFmt,
            PrefixTagged (U8,
            46,
            FractionFmt)))),
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

    impl SpecParser for FractionOneFmt {
        type PVal = FractionOneSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for FractionOneFmt {
        type Val = FractionOneSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for FractionOneFmt {
        type SValue = FractionOneSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for FractionOneFmt {
        type SVal = FractionOneSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for FractionOneFmt {
        type T = FractionOneSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for FractionTwoFmt {
        type PVal = FractionTwoSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for FractionTwoFmt {
        type Val = FractionTwoSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for FractionTwoFmt {
        type SValue = FractionTwoSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for FractionTwoFmt {
        type SVal = FractionTwoSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for FractionTwoFmt {
        type T = FractionTwoSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for FractionThreeFmt {
        type PVal = FractionThreeSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for FractionThreeFmt {
        type Val = FractionThreeSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for FractionThreeFmt {
        type SValue = FractionThreeSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for FractionThreeFmt {
        type SVal = FractionThreeSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for FractionThreeFmt {
        type T = FractionThreeSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for FractionFourFmt {
        type PVal = FractionFourSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for FractionFourFmt {
        type Val = FractionFourSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for FractionFourFmt {
        type SValue = FractionFourSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for FractionFourFmt {
        type SVal = FractionFourSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for FractionFourFmt {
        type T = FractionFourSpec ;
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
        FractionSpec::lemma_from_into,
        FractionSpec::lemma_into_from,
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

    impl SafeParser for FractionOneFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for FractionOneFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for FractionOneFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecParser>::spec_parse) ;
            reveal(< FractionOneFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecParser>::spec_parse) ;
            reveal(< FractionOneFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for FractionOneFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionOneFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for FractionOneFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< FractionOneFmt as SpecSerializer>::spec_serialize) ;
            reveal(< FractionOneFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for FractionOneFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecParser>::spec_parse) ;
            reveal(< FractionOneFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionOneFmt as Consistency>::consistent) ;
            reveal(< FractionOneFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for FractionOneFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for FractionOneFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< FractionOneFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionOneFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for FractionOneFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< FractionOneFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionOneFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for FractionTwoFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for FractionTwoFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for FractionTwoFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecParser>::spec_parse) ;
            reveal(< FractionTwoFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecParser>::spec_parse) ;
            reveal(< FractionTwoFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for FractionTwoFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionTwoFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for FractionTwoFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< FractionTwoFmt as SpecSerializer>::spec_serialize) ;
            reveal(< FractionTwoFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for FractionTwoFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecParser>::spec_parse) ;
            reveal(< FractionTwoFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionTwoFmt as Consistency>::consistent) ;
            reveal(< FractionTwoFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for FractionTwoFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for FractionTwoFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< FractionTwoFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionTwoFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for FractionTwoFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< FractionTwoFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionTwoFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for FractionThreeFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for FractionThreeFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for FractionThreeFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecParser>::spec_parse) ;
            reveal(< FractionThreeFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecParser>::spec_parse) ;
            reveal(< FractionThreeFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for FractionThreeFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionThreeFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for FractionThreeFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< FractionThreeFmt as SpecSerializer>::spec_serialize) ;
            reveal(< FractionThreeFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for FractionThreeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecParser>::spec_parse) ;
            reveal(< FractionThreeFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionThreeFmt as Consistency>::consistent) ;
            reveal(< FractionThreeFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for FractionThreeFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for FractionThreeFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< FractionThreeFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionThreeFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for FractionThreeFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< FractionThreeFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionThreeFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for FractionFourFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for FractionFourFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for FractionFourFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecParser>::spec_parse) ;
            reveal(< FractionFourFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecParser>::spec_parse) ;
            reveal(< FractionFourFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for FractionFourFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFourFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for FractionFourFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< FractionFourFmt as SpecSerializer>::spec_serialize) ;
            reveal(< FractionFourFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for FractionFourFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecParser>::spec_parse) ;
            reveal(< FractionFourFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFourFmt as Consistency>::consistent) ;
            reveal(< FractionFourFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for FractionFourFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for FractionFourFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< FractionFourFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFourFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for FractionFourFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< FractionFourFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< FractionFourFmt as SpecSerializer>::spec_serialize) ;
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
            assert forall | input: FractionInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                FractionSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< FractionFmt as SpecParser>::spec_parse) ;
            reveal(< FractionFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: FractionInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                FractionSpec::lemma_into_from (input) ;
            }
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
            assert forall | output: FractionSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                FractionSpec::lemma_from_into (output) ;
            }
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
            assert forall | input: FractionInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                FractionSpec::lemma_into_from (input) ;
            }
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



    impl<'i> Parser<&'i [u8]> for FractionOneFmt {
        type PT = FractionOne;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FractionOneFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = AndThen (Tail, Array::< 1, _ > (DigitFmt)).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FractionOne> for FractionOneFmt {
        fn serialize_into(&self, v: &FractionOne, obuf: &mut Output) {
            reveal(<FractionOneFmt as SpecSerializer>::spec_serialize);
            reveal(<FractionOneFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            AndThen (Tail, Array::< 1, _ > (DigitFmt)).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FractionOne> for FractionOneFmt {
        fn prepare(&self, v: &FractionOne) -> Result<usize, PreSerializeError> {
            broadcast use vest_lib::combinators::bytes::spec::tail_and_then_lemmas;
            reveal(<FractionOneFmt as SpecByteLen>::byte_len);
            (AndThen (Tail, Array::< 1, _ > (DigitFmt))).prepare (v)
        }
    }



    impl<'i> Parser<&'i [u8]> for FractionTwoFmt {
        type PT = FractionTwo;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FractionTwoFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = AndThen (Tail, Array::< 2, _ > (DigitFmt)).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FractionTwo> for FractionTwoFmt {
        fn serialize_into(&self, v: &FractionTwo, obuf: &mut Output) {
            reveal(<FractionTwoFmt as SpecSerializer>::spec_serialize);
            reveal(<FractionTwoFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            AndThen (Tail, Array::< 2, _ > (DigitFmt)).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FractionTwo> for FractionTwoFmt {
        fn prepare(&self, v: &FractionTwo) -> Result<usize, PreSerializeError> {
            broadcast use vest_lib::combinators::bytes::spec::tail_and_then_lemmas;
            reveal(<FractionTwoFmt as SpecByteLen>::byte_len);
            (AndThen (Tail, Array::< 2, _ > (DigitFmt))).prepare (v)
        }
    }



    impl<'i> Parser<&'i [u8]> for FractionThreeFmt {
        type PT = FractionThree;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FractionThreeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = AndThen (Tail, Array::< 3, _ > (DigitFmt)).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FractionThree> for FractionThreeFmt {
        fn serialize_into(&self, v: &FractionThree, obuf: &mut Output) {
            reveal(<FractionThreeFmt as SpecSerializer>::spec_serialize);
            reveal(<FractionThreeFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            AndThen (Tail, Array::< 3, _ > (DigitFmt)).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FractionThree> for FractionThreeFmt {
        fn prepare(&self, v: &FractionThree) -> Result<usize, PreSerializeError> {
            broadcast use vest_lib::combinators::bytes::spec::tail_and_then_lemmas;
            reveal(<FractionThreeFmt as SpecByteLen>::byte_len);
            (AndThen (Tail, Array::< 3, _ > (DigitFmt))).prepare (v)
        }
    }



    impl<'i> Parser<&'i [u8]> for FractionFourFmt {
        type PT = FractionFour;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FractionFourFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = AndThen (Tail, Array::< 4, _ > (DigitFmt)).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FractionFour> for FractionFourFmt {
        fn serialize_into(&self, v: &FractionFour, obuf: &mut Output) {
            reveal(<FractionFourFmt as SpecSerializer>::spec_serialize);
            reveal(<FractionFourFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            AndThen (Tail, Array::< 4, _ > (DigitFmt)).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FractionFour> for FractionFourFmt {
        fn prepare(&self, v: &FractionFour) -> Result<usize, PreSerializeError> {
            broadcast use vest_lib::combinators::bytes::spec::tail_and_then_lemmas;
            reveal(<FractionFourFmt as SpecByteLen>::byte_len);
            (AndThen (Tail, Array::< 4, _ > (DigitFmt))).prepare (v)
        }
    }



    impl<'i> Parser<&'i [u8]> for FractionFmt {
        type PT = Fraction;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FractionFmt as SpecParser>::spec_parse);
            reveal(<Fraction as DeepView>::deep_view);
            reveal(FractionSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (Named ("fraction_one", FractionOneFmt)).parse (& rest) {
        Ok ((n,
        va)) => {
            Ok ((n,
            Fraction::One (va)))
        }
       ,
        _ => match (Named ("fraction_two",
        FractionTwoFmt)).parse (& rest) {
            Ok ((n,
            va)) => {
                Ok ((n,
                Fraction::Two (va)))
            }
           ,
            _ => match (Named ("fraction_three",
            FractionThreeFmt)).parse (& rest) {
                Ok ((n,
                va)) => {
                    Ok ((n,
                    Fraction::Three (va)))
                }
               ,
                _ => match (Named ("fraction_four",
                FractionFourFmt)).parse (& rest) {
                    Ok ((n,
                    va)) => {
                        Ok ((n,
                        Fraction::Four (va)))
                    }
                   ,
                    _ => Err (ParseError::invalid_choice()),
                }
               ,
            }
           ,
        }
       ,
    }
    ?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Fraction> for FractionFmt {
        fn serialize_into(&self, v: &Fraction, obuf: &mut Output) {
            reveal(<FractionFmt as SpecSerializer>::spec_serialize);
            reveal(<FractionFmt as SpecByteLen>::byte_len);
            reveal(<Fraction as DeepView>::deep_view);
            reveal(FractionSpec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                Fraction::One (v) => {
                    (FractionOneFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                Fraction::Two (v) => {
                    (FractionTwoFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                Fraction::Three (v) => {
                    (FractionThreeFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                Fraction::Four (v) => {
                    (FractionFourFmt).serialize_into (v,
                    obuf) ;
                }
                ,
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Fraction> for FractionFmt {
        fn prepare(&self, v: &Fraction) -> Result<usize, PreSerializeError> {
            reveal(<FractionFmt as SpecByteLen>::byte_len);
            reveal(<Fraction as DeepView>::deep_view);
            reveal(FractionSpec::into_structural);
            match v {
                Fraction::One (v) => (Named ("fraction_one", FractionOneFmt)).prepare (v),
                Fraction::Two (v) => (Named ("fraction_two", FractionTwoFmt)).prepare (v),
                Fraction::Three (v) => (Named ("fraction_three", FractionThreeFmt)).prepare (v),
                Fraction::Four (v) => (Named ("fraction_four", FractionFourFmt)).prepare (v),
            }
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

            let (n1, sign) = (Opt (PrefixTagged (U8, 45, Empty))).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, natural_first) = (Named ("digit", DigitFmt)).parse (& rest) ?;
            if !(natural_first >= 48 && natural_first <= 57) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n2);
            let (n3, natural_following_digits) = (Star (DigitFmt)).parse (& rest) ?;
            let rest = rest.skip(n3);
            let (n4, fraction) = (PrefixTagged (U8, 46, FractionFmt)).parse (& rest) ?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = Decimal {
                sign,
                natural_first,
                natural_following_digits,
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
                sign,
                natural_first,
                natural_following_digits,
                fraction,
            } = v;
            Opt (PrefixTagged (U8, 45, Empty)).serialize_into(sign, obuf);
            DigitFmt.serialize_into(natural_first, obuf);
            Star (DigitFmt).serialize_into(natural_following_digits, obuf);
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
                sign,
                natural_first,
                natural_following_digits,
                fraction,
            } = v;
            let l1 = (Opt (PrefixTagged (U8, 45, Empty))).prepare (sign) ?;
            let l2 = {
                if ! (* natural_first >= 48 && * natural_first <= 57) {
                    Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                }
                else {
                    (Named ("digit",
                    DigitFmt)).prepare (natural_first)
                }
            }
            ?;
            let l3 = (Star (DigitFmt)).prepare (natural_following_digits) ?;
            let l4 = (PrefixTagged (U8, 46, FractionFmt)).prepare (fraction) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l4).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
