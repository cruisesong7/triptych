// Implementation of Triptych's generated external-parser contract.

use vstd::prelude::*;

use crate::ipv4::contract::IPv4ExternalParserContract;
#[cfg(verus_only)]
use crate::ipv4::spec::ipv4_is_valid;
#[cfg(verus_only)]
use crate::ipv4::spec as ipv4_spec;
use crate::ipv6::contract::IPv6ExternalParserContract;
#[cfg(verus_only)]
use crate::ipv6::spec::ipv6_is_valid;
#[cfg(verus_only)]
use crate::ipv6::spec as ipv6_spec;
#[cfg(verus_only)]
use crate::model::ipaddr_parse_spec;
#[cfg(verus_only)]
use crate::model::{
    ipaddr_contains, ipaddr_decimal_nat, ipaddr_digit_value, ipaddr_find_slash,
    ipaddr_hex_value, ipaddr_is_digit, ipaddr_ipv4_state,
    ipaddr_ipv6_state, ipaddr_parse_prefix,
};
use crate::optimized::IpAddrParser;
#[cfg(verus_only)]
use crate::printer::{
    ipv4_canonical_characters, ipv4_canonical_matches_result,
    ipv6_address_space, ipv6_canonical_characters,
    ipv6_canonical_matches_result, ipv6_generated_address_space,
    ipv6_hex_seq_from_concat_suffix,
};
#[cfg(verus_only)]
use vstd::arithmetic::mul::{
    lemma_mul_is_commutative, lemma_mul_left_inequality,
};
#[cfg(verus_only)]
use vstd::assert_seqs_equal;
#[cfg(verus_only)]
use vstd::utf8::is_ascii_chars;

verus! {

pub proof fn ipv6_hex_digit_matches(character: char)
    requires
        ipv6_spec::triptych_is_hex_digit(character),
    ensures
        ipaddr_hex_value(character)
            == Some(ipv6_spec::triptych_hex_digit_value(character)),
        0 <= ipv6_spec::triptych_hex_digit_value(character) <= 15,
{
    reveal(ipv6_spec::triptych_is_hex_digit);
    reveal(ipv6_spec::triptych_is_digit);
    reveal(ipv6_spec::triptych_hex_digit_value);
    reveal(ipaddr_hex_value);
}

pub proof fn ipv6_model_hex_digit_matches(character: char, value: int)
    requires
        ipaddr_hex_value(character) == Some(value),
    ensures
        ipv6_spec::triptych_is_hex_digit(character),
        ipv6_spec::triptych_hex_digit_value(character) == value,
        0 <= value <= 15,
{
    reveal(ipaddr_hex_value);
    reveal(ipv6_spec::triptych_is_hex_digit);
    reveal(ipv6_spec::triptych_is_digit);
    reveal(ipv6_spec::triptych_hex_digit_value);
}

pub proof fn ipv4_digit_implies_ipv6_digit(character: char)
    requires
        ipv4_spec::triptych_is_digit(character),
    ensures
        ipv6_spec::triptych_is_digit(character),
{
    reveal(ipv4_spec::triptych_is_digit);
    reveal(ipv6_spec::triptych_is_digit);
}

#[verifier::spinoff_prover]
pub proof fn ipv6_consume_hextet(
    input: Seq<char>,
    start: int,
    index: int,
    end: int,
    left: int,
    right: int,
    left_count: int,
    right_count: int,
    compressed: bool,
    hextet: Seq<char>,
)
    requires
        0 <= start <= index,
        index + hextet.len() <= end <= input.len(),
        0 <= left,
        0 <= right,
        0 <= left_count <= 8,
        0 <= right_count <= 8,
        input.subrange(index, index + hextet.len() as int) == hextet,
        1 <= hextet.len() <= 4,
        forall|checked: int| 0 <= checked < hextet.len() ==>
            #[trigger] ipv6_spec::triptych_is_hex_digit(hextet[checked]),
    ensures
        0 <= ipv6_spec::triptych_hex_seq_of(hextet) <= 65_535,
        ipaddr_ipv6_state(
            input,
            start,
            index,
            end,
            left,
            right,
            left_count,
            right_count,
            compressed,
            0,
            0,
        ) == ipaddr_ipv6_state(
            input,
            start,
            index + hextet.len() as int,
            end,
            left,
            right,
            left_count,
            right_count,
            compressed,
            ipv6_spec::triptych_hex_seq_of(hextet),
            hextet.len() as int,
        ),
{
    reveal(ipv6_spec::triptych_hex_seq_of);
    if hextet.len() == 1 {
        assert(input[index] == hextet[0]);
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        ipv6_hex_digit_matches(hextet[0]);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
        reveal_with_fuel(ipaddr_ipv6_state, 1);
    } else if hextet.len() == 2 {
        assert(input[index] == hextet[0]);
        assert(input[index + 1] == hextet[1]);
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[1]));
        ipv6_hex_digit_matches(hextet[0]);
        ipv6_hex_digit_matches(hextet[1]);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 3);
        reveal_with_fuel(ipaddr_ipv6_state, 2);
    } else if hextet.len() == 3 {
        assert(input[index] == hextet[0]);
        assert(input[index + 1] == hextet[1]);
        assert(input[index + 2] == hextet[2]);
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[1]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[2]));
        ipv6_hex_digit_matches(hextet[0]);
        ipv6_hex_digit_matches(hextet[1]);
        ipv6_hex_digit_matches(hextet[2]);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 4);
        reveal_with_fuel(ipaddr_ipv6_state, 3);
    } else {
        assert(hextet.len() == 4);
        assert(input[index] == hextet[0]);
        assert(input[index + 1] == hextet[1]);
        assert(input[index + 2] == hextet[2]);
        assert(input[index + 3] == hextet[3]);
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[1]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[2]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[3]));
        ipv6_hex_digit_matches(hextet[0]);
        ipv6_hex_digit_matches(hextet[1]);
        ipv6_hex_digit_matches(hextet[2]);
        ipv6_hex_digit_matches(hextet[3]);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 5);
        reveal_with_fuel(ipaddr_ipv6_state, 4);
    }
}

#[verifier::spinoff_prover]
pub proof fn ipv6_hex_seq_hextet_prefix(
    hextet: Seq<char>,
    suffix: Seq<char>,
    accumulator: int,
)
    requires
        1 <= hextet.len() <= 4,
        forall|checked: int| 0 <= checked < hextet.len() ==>
            #[trigger] ipv6_spec::triptych_is_hex_digit(hextet[checked]),
    ensures
        ipv6_spec::triptych_hex_seq_from(
            hextet + suffix,
            0,
            accumulator,
            0,
        ) == ipv6_spec::triptych_hex_seq_from(
            suffix,
            0,
            accumulator,
            ipv6_spec::triptych_hex_seq_of(hextet),
        ),
{
    reveal(ipv6_spec::triptych_hex_seq_of);
    if hextet.len() == 1 {
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        assert((hextet + suffix)[0] == hextet[0]);
        ipv6_hex_seq_from_concat_suffix(
            hextet,
            suffix,
            0,
            accumulator,
            ipv6_spec::triptych_hex_digit_value(hextet[0]),
        );
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
    } else if hextet.len() == 2 {
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[1]));
        ipv6_hex_seq_from_concat_suffix(
            hextet,
            suffix,
            0,
            accumulator,
            ipv6_spec::triptych_hex_digit_value(hextet[0]) * 16
                + ipv6_spec::triptych_hex_digit_value(hextet[1]),
        );
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 3);
    } else if hextet.len() == 3 {
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[1]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[2]));
        ipv6_hex_seq_from_concat_suffix(
            hextet,
            suffix,
            0,
            accumulator,
            (ipv6_spec::triptych_hex_digit_value(hextet[0]) * 16
                + ipv6_spec::triptych_hex_digit_value(hextet[1])) * 16
                + ipv6_spec::triptych_hex_digit_value(hextet[2]),
        );
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 4);
    } else {
        assert(hextet.len() == 4);
        assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[1]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[2]));
        assert(ipv6_spec::triptych_is_hex_digit(hextet[3]));
        ipv6_hex_seq_from_concat_suffix(
            hextet,
            suffix,
            0,
            accumulator,
            ((ipv6_spec::triptych_hex_digit_value(hextet[0]) * 16
                + ipv6_spec::triptych_hex_digit_value(hextet[1])) * 16
                + ipv6_spec::triptych_hex_digit_value(hextet[2])) * 16
                + ipv6_spec::triptych_hex_digit_value(hextet[3]),
        );
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 5);
    }
}

pub proof fn ipv6_segments_suffix_extensional(
    prefix: Seq<char>,
    suffix: Seq<char>,
    index: int,
    count: int,
)
    requires
        0 <= index <= suffix.len(),
    ensures
        ipv6_spec::triptych_segments_from(
            prefix + suffix,
            prefix.len() as int + index,
            count,
        ) == ipv6_spec::triptych_segments_from(
            suffix,
            index,
            count,
        ),
    decreases suffix.len() - index,
{
    if index < suffix.len() {
        assert(
            (prefix + suffix)[prefix.len() as int + index]
                == suffix[index]
        );
        let next_count =
            if suffix[index] == ':' { count + 1 } else { count };
        ipv6_segments_suffix_extensional(
            prefix,
            suffix,
            index + 1,
            next_count,
        );
    }
    reveal(ipv6_spec::triptych_segments_from);
}

pub proof fn ipv6_segments_skip_non_colon(
    prefix: Seq<char>,
    suffix: Seq<char>,
    index: int,
    count: int,
)
    requires
        0 <= index <= prefix.len(),
        forall|checked: int| index <= checked < prefix.len() ==>
            #[trigger] prefix[checked] != ':',
    ensures
        ipv6_spec::triptych_segments_from(
            prefix + suffix,
            index,
            count,
        ) == ipv6_spec::triptych_segments_from(
            suffix,
            0,
            count,
        ),
    decreases prefix.len() - index,
{
    if index < prefix.len() {
        assert((prefix + suffix)[index] == prefix[index]);
        assert(prefix[index] != ':');
        assert forall|checked: int|
            index + 1 <= checked < prefix.len() implies
                #[trigger] prefix[checked] != ':' by {}
        ipv6_segments_skip_non_colon(
            prefix,
            suffix,
            index + 1,
            count,
        );
        reveal(ipv6_spec::triptych_segments_from);
    } else {
        ipv6_segments_suffix_extensional(
            prefix,
            suffix,
            0,
            count,
        );
    }
}

pub proof fn ipv6_segments_add_count(
    characters: Seq<char>,
    index: int,
    count: int,
    extra: int,
)
    requires
        0 <= index <= characters.len(),
    ensures
        ipv6_spec::triptych_segments_from(
            characters,
            index,
            count + extra,
        ) == ipv6_spec::triptych_segments_from(
            characters,
            index,
            count,
        ) + extra,
    decreases characters.len() - index,
{
    if index < characters.len() {
        let next_count =
            if characters[index] == ':' { count + 1 } else { count };
        ipv6_segments_add_count(
            characters,
            index + 1,
            next_count,
            extra,
        );
    }
    reveal(ipv6_spec::triptych_segments_from);
}

pub proof fn ipv6_hextet_segments(hextet: Seq<char>)
    requires
        0 < hextet.len(),
        forall|checked: int| 0 <= checked < hextet.len() ==>
            #[trigger] ipv6_spec::triptych_is_hex_digit(
                hextet[checked],
            ),
    ensures
        ipv6_spec::triptych_segments_of(hextet) == 1,
{
    assert forall|checked: int| 0 <= checked < hextet.len() implies
        #[trigger] hextet[checked] != ':' by {
        assert(ipv6_spec::triptych_is_hex_digit(hextet[checked]));
        reveal(ipv6_spec::triptych_is_hex_digit);
        reveal(ipv6_spec::triptych_is_digit);
    }
    let empty = Seq::<char>::empty();
    ipv6_segments_skip_non_colon(hextet, empty, 0, 1);
    reveal(ipv6_spec::triptych_segments_of);
    reveal(ipv6_spec::triptych_segments_from);
}

pub proof fn ipv6_segments_hextet_colon_tail(
    hextet: Seq<char>,
    tail: Seq<char>,
)
    requires
        0 < hextet.len(),
        0 < tail.len(),
        forall|checked: int| 0 <= checked < hextet.len() ==>
            #[trigger] ipv6_spec::triptych_is_hex_digit(
                hextet[checked],
            ),
    ensures
        ipv6_spec::triptych_segments_of(
            hextet + seq![':'] + tail,
        ) == 1 + ipv6_spec::triptych_segments_of(tail),
{
    assert forall|checked: int| 0 <= checked < hextet.len() implies
        #[trigger] hextet[checked] != ':' by {
        assert(ipv6_spec::triptych_is_hex_digit(hextet[checked]));
        reveal(ipv6_spec::triptych_is_hex_digit);
        reveal(ipv6_spec::triptych_is_digit);
    }
    let colon_tail = seq![':'] + tail;
    ipv6_segments_skip_non_colon(
        hextet,
        colon_tail,
        0,
        1,
    );
    ipv6_segments_suffix_extensional(
        seq![':'],
        tail,
        0,
        2,
    );
    ipv6_segments_add_count(tail, 0, 1, 1);
    assert(
        hextet + seq![':'] + tail == hextet + colon_tail
    ) by {
        assert_seqs_equal!(
            hextet + seq![':'] + tail == hextet + colon_tail
        );
    }
    assert(
        ipv6_spec::triptych_segments_from(
            hextet + colon_tail,
            0,
            1,
        ) == ipv6_spec::triptych_segments_from(
            colon_tail,
            0,
            1,
        )
    );
    assert(colon_tail[0] == ':');
    assert(
        ipv6_spec::triptych_segments_from(
            colon_tail,
            0,
            1,
        ) == ipv6_spec::triptych_segments_from(
            colon_tail,
            1,
            2,
        )
    ) by {
        reveal_with_fuel(
            ipv6_spec::triptych_segments_from,
            1,
        );
    }
    assert(
        ipv6_spec::triptych_segments_from(
            colon_tail,
            1,
            2,
        ) == ipv6_spec::triptych_segments_from(
            tail,
            0,
            2,
        )
    );
    assert(
        ipv6_spec::triptych_segments_from(
            tail,
            0,
            2,
        ) == ipv6_spec::triptych_segments_from(
            tail,
            0,
            1,
        ) + 1
    );
    reveal(ipv6_spec::triptych_segments_of);
}

pub proof fn ipaddr_ipv6_state_prefix_extensional(
    input: Seq<char>,
    prefix: Seq<char>,
    start: int,
    index: int,
    end: int,
    left: int,
    right: int,
    left_count: int,
    right_count: int,
    compressed: bool,
    hextet: int,
    digits: int,
)
    requires
        0 <= start <= index <= end <= input.len(),
        end == prefix.len(),
        input.subrange(0, end) == prefix,
    ensures
        ipaddr_ipv6_state(
            input,
            start,
            index,
            end,
            left,
            right,
            left_count,
            right_count,
            compressed,
            hextet,
            digits,
        ) == ipaddr_ipv6_state(
            prefix,
            start,
            index,
            end,
            left,
            right,
            left_count,
            right_count,
            compressed,
            hextet,
            digits,
        ),
    decreases end - index,
{
    if index < end {
        assert(input[index] == prefix[index]);
        match ipaddr_hex_value(input[index]) {
            Some(digit) => {
                if digits != 4 {
                    ipaddr_ipv6_state_prefix_extensional(
                        input,
                        prefix,
                        start,
                        index + 1,
                        end,
                        left,
                        right,
                        left_count,
                        right_count,
                        compressed,
                        hextet * 16 + digit,
                        digits + 1,
                    );
                }
            },
            None => {
                if input[index] == ':' {
                    if digits == 0 {
                        if index == start
                            && index + 1 < end
                            && input[index + 1] == ':'
                            && !compressed
                        {
                            assert(
                                input[index + 1]
                                    == prefix[index + 1]
                            );
                            ipaddr_ipv6_state_prefix_extensional(
                                input,
                                prefix,
                                start,
                                index + 2,
                                end,
                                left,
                                right,
                                left_count,
                                right_count,
                                true,
                                0,
                                0,
                            );
                        }
                    } else {
                        let next_left = if compressed {
                            left
                        } else {
                            left * 65_536 + hextet
                        };
                        let next_right = if compressed {
                            right * 65_536 + hextet
                        } else {
                            right
                        };
                        let next_left_count =
                            if compressed { left_count } else {
                                left_count + 1
                            };
                        let next_right_count =
                            if compressed { right_count + 1 } else {
                                right_count
                            };
                        if next_left_count <= 8
                            && next_right_count <= 8
                        {
                            if index + 1 < end
                                && input[index + 1] == ':'
                            {
                                assert(
                                    input[index + 1]
                                        == prefix[index + 1]
                                );
                                if !compressed {
                                    ipaddr_ipv6_state_prefix_extensional(
                                        input,
                                        prefix,
                                        start,
                                        index + 2,
                                        end,
                                        next_left,
                                        next_right,
                                        next_left_count,
                                        next_right_count,
                                        true,
                                        0,
                                        0,
                                    );
                                }
                            } else if index + 1 < end {
                                ipaddr_ipv6_state_prefix_extensional(
                                    input,
                                    prefix,
                                    start,
                                    index + 1,
                                    end,
                                    next_left,
                                    next_right,
                                    next_left_count,
                                    next_right_count,
                                    compressed,
                                    0,
                                    0,
                                );
                            }
                        }
                    }
                }
            },
        }
    }
    reveal(ipaddr_ipv6_state);
}

pub proof fn ipv6_rep0_starts_hex(input: Seq<char>, count: int)
    requires
        0 <= count,
        ipv6_spec::ipv6_rep_0_matches(input, count),
    ensures
        0 < input.len(),
        ipv6_spec::triptych_is_hex_digit(input[0]),
{
    reveal(ipv6_spec::ipv6_rep_0_matches);
    let split = choose|split: int|
        0 <= split <= input.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16(
                input.subrange(0, split),
            )
            && (
                (8 <= count + 1
                    && count + 1 <= 8
                    && split == input.len())
                || (count + 1 < 8
                    && split + 1 <= input.len()
                    && input.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_0_matches(
                        input.subrange(split + 1, input.len() as int),
                        count + 1,
                    ))
            );
    let hextet = input.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16);
    assert(1 <= hextet.len() <= 4);
    assert forall|index: int| 0 <= index < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[index],
        ) by {}
    assert(0 < split);
    assert(input[0] == hextet[0]);
    assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
}

pub proof fn ipv6_rep1_starts_hex(input: Seq<char>, count: int)
    requires
        0 <= count,
        ipv6_spec::ipv6_rep_1_matches(input, count),
    ensures
        0 < input.len(),
        ipv6_spec::triptych_is_hex_digit(input[0]),
{
    reveal(ipv6_spec::ipv6_rep_1_matches);
    let split = choose|split: int|
        0 <= split <= input.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16L(
                input.subrange(0, split),
            )
            && (
                (1 <= count + 1
                    && count + 1 <= 7
                    && split == input.len())
                || (count + 1 < 7
                    && split + 1 <= input.len()
                    && input.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_1_matches(
                        input.subrange(split + 1, input.len() as int),
                        count + 1,
                    ))
            );
    let hextet = input.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16L);
    assert(1 <= hextet.len() <= 4);
    assert forall|index: int| 0 <= index < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[index],
        ) by {}
    assert(0 < split);
    assert(input[0] == hextet[0]);
    assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
}

pub proof fn ipv6_rep2_starts_hex(input: Seq<char>, count: int)
    requires
        0 <= count,
        ipv6_spec::ipv6_rep_2_matches(input, count),
    ensures
        0 < input.len(),
        ipv6_spec::triptych_is_hex_digit(input[0]),
{
    reveal(ipv6_spec::ipv6_rep_2_matches);
    let split = choose|split: int|
        0 <= split <= input.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16R(
                input.subrange(0, split),
            )
            && (
                (1 <= count + 1
                    && count + 1 <= 7
                    && split == input.len())
                || (count + 1 < 7
                    && split + 1 <= input.len()
                    && input.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_2_matches(
                        input.subrange(split + 1, input.len() as int),
                        count + 1,
                    ))
            );
    let hextet = input.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16R);
    assert(1 <= hextet.len() <= 4);
    assert forall|index: int| 0 <= index < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[index],
        ) by {}
    assert(0 < split);
    assert(input[0] == hextet[0]);
    assert(ipv6_spec::triptych_is_hex_digit(hextet[0]));
}

pub open spec fn ipv6_address_alphabet(input: Seq<char>) -> bool {
    forall|index: int| 0 <= index < input.len() ==>
        #[trigger] ipv6_spec::triptych_is_hex_digit(input[index])
            || input[index] == ':'
}

#[verifier::rlimit(100)]
pub proof fn ipv6_rep0_properties(input: Seq<char>, count: int)
    requires
        0 <= count < 8,
        ipv6_spec::ipv6_rep_0_matches(input, count),
    ensures
        0 < input.len(),
        ipv6_address_alphabet(input),
        ipv6_spec::triptych_segments_of(input) == 8 - count,
        input.len() <= 5 * ipv6_spec::triptych_segments_of(input) - 1,
    decreases input.len(),
{
    reveal(ipv6_spec::ipv6_rep_0_matches);
    let split = choose|split: int|
        0 <= split <= input.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16(
                input.subrange(0, split),
            )
            && (
                (8 <= count + 1
                    && count + 1 <= 8
                    && split == input.len())
                || (count + 1 < 8
                    && split + 1 <= input.len()
                    && input.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_0_matches(
                        input.subrange(split + 1, input.len() as int),
                        count + 1,
                    ))
            );
    let hextet = input.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16);
    assert(1 <= hextet.len() <= 4);
    assert forall|position: int| 0 <= position < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[position],
        ) by {}
    if split == input.len() {
        assert(count == 7);
        assert(input == hextet) by {
            assert_seqs_equal!(input == hextet);
        }
        ipv6_hextet_segments(hextet);
        assert(ipv6_address_alphabet(input)) by {
            reveal(ipv6_address_alphabet);
        }
    } else {
        let tail =
            input.subrange(split + 1, input.len() as int);
        assert(count + 1 < 8);
        assert(input.subrange(split, split + 1)[0] == ':');
        assert(input[split] == ':');
        ipv6_rep0_properties(tail, count + 1);
        assert(0 < tail.len());
        assert(input == hextet + seq![':'] + tail) by {
            assert_seqs_equal!(
                input == hextet + seq![':'] + tail
            );
        }
        ipv6_segments_hextet_colon_tail(hextet, tail);
        assert(ipv6_address_alphabet(input)) by {
            reveal(ipv6_address_alphabet);
            assert forall|index: int| 0 <= index < input.len() implies
                #[trigger] ipv6_spec::triptych_is_hex_digit(
                    input[index],
                ) || input[index] == ':' by {
                if index < hextet.len() {
                    assert(input[index] == hextet[index]);
                } else if index == hextet.len() {
                    assert(input[index] == ':');
                } else {
                    let tail_index = index - hextet.len() - 1;
                    assert(0 <= tail_index < tail.len());
                    assert(input[index] == tail[tail_index]);
                    assert(ipv6_address_alphabet(tail));
                }
            }
        }
    }
}

#[verifier::rlimit(100)]
pub proof fn ipv6_rep1_properties(input: Seq<char>, count: int)
    requires
        0 <= count < 7,
        ipv6_spec::ipv6_rep_1_matches(input, count),
    ensures
        0 < input.len(),
        ipv6_address_alphabet(input),
        1 <= ipv6_spec::triptych_segments_of(input) <= 7 - count,
        input.len() <= 5 * ipv6_spec::triptych_segments_of(input) - 1,
    decreases input.len(),
{
    reveal(ipv6_spec::ipv6_rep_1_matches);
    let split = choose|split: int|
        0 <= split <= input.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16L(
                input.subrange(0, split),
            )
            && (
                (1 <= count + 1
                    && count + 1 <= 7
                    && split == input.len())
                || (count + 1 < 7
                    && split + 1 <= input.len()
                    && input.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_1_matches(
                        input.subrange(split + 1, input.len() as int),
                        count + 1,
                    ))
            );
    let hextet = input.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16L);
    assert(1 <= hextet.len() <= 4);
    assert forall|position: int| 0 <= position < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[position],
        ) by {}
    if split == input.len() {
        assert(input == hextet) by {
            assert_seqs_equal!(input == hextet);
        }
        ipv6_hextet_segments(hextet);
        assert(ipv6_address_alphabet(input)) by {
            reveal(ipv6_address_alphabet);
        }
    } else {
        let tail =
            input.subrange(split + 1, input.len() as int);
        assert(count + 1 < 7);
        assert(input.subrange(split, split + 1)[0] == ':');
        assert(input[split] == ':');
        ipv6_rep1_properties(tail, count + 1);
        assert(0 < tail.len());
        assert(input == hextet + seq![':'] + tail) by {
            assert_seqs_equal!(
                input == hextet + seq![':'] + tail
            );
        }
        ipv6_segments_hextet_colon_tail(hextet, tail);
        assert(ipv6_address_alphabet(input)) by {
            reveal(ipv6_address_alphabet);
            assert forall|index: int| 0 <= index < input.len() implies
                #[trigger] ipv6_spec::triptych_is_hex_digit(
                    input[index],
                ) || input[index] == ':' by {
                if index < hextet.len() {
                    assert(input[index] == hextet[index]);
                } else if index == hextet.len() {
                    assert(input[index] == ':');
                } else {
                    let tail_index = index - hextet.len() - 1;
                    assert(0 <= tail_index < tail.len());
                    assert(input[index] == tail[tail_index]);
                    assert(ipv6_address_alphabet(tail));
                }
            }
        }
    }
}

#[verifier::rlimit(100)]
pub proof fn ipv6_rep2_properties(input: Seq<char>, count: int)
    requires
        0 <= count < 7,
        ipv6_spec::ipv6_rep_2_matches(input, count),
    ensures
        0 < input.len(),
        ipv6_address_alphabet(input),
        1 <= ipv6_spec::triptych_segments_of(input) <= 7 - count,
        input.len() <= 5 * ipv6_spec::triptych_segments_of(input) - 1,
    decreases input.len(),
{
    reveal(ipv6_spec::ipv6_rep_2_matches);
    let split = choose|split: int|
        0 <= split <= input.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16R(
                input.subrange(0, split),
            )
            && (
                (1 <= count + 1
                    && count + 1 <= 7
                    && split == input.len())
                || (count + 1 < 7
                    && split + 1 <= input.len()
                    && input.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_2_matches(
                        input.subrange(split + 1, input.len() as int),
                        count + 1,
                    ))
            );
    let hextet = input.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16R);
    assert(1 <= hextet.len() <= 4);
    assert forall|position: int| 0 <= position < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[position],
        ) by {}
    if split == input.len() {
        assert(input == hextet) by {
            assert_seqs_equal!(input == hextet);
        }
        ipv6_hextet_segments(hextet);
        assert(ipv6_address_alphabet(input)) by {
            reveal(ipv6_address_alphabet);
        }
    } else {
        let tail =
            input.subrange(split + 1, input.len() as int);
        assert(count + 1 < 7);
        assert(input.subrange(split, split + 1)[0] == ':');
        assert(input[split] == ':');
        ipv6_rep2_properties(tail, count + 1);
        assert(0 < tail.len());
        assert(input == hextet + seq![':'] + tail) by {
            assert_seqs_equal!(
                input == hextet + seq![':'] + tail
            );
        }
        ipv6_segments_hextet_colon_tail(hextet, tail);
        assert(ipv6_address_alphabet(input)) by {
            reveal(ipv6_address_alphabet);
            assert forall|index: int| 0 <= index < input.len() implies
                #[trigger] ipv6_spec::triptych_is_hex_digit(
                    input[index],
                ) || input[index] == ':' by {
                if index < hextet.len() {
                    assert(input[index] == hextet[index]);
                } else if index == hextet.len() {
                    assert(input[index] == ':');
                } else {
                    let tail_index = index - hextet.len() - 1;
                    assert(0 <= tail_index < tail.len());
                    assert(input[index] == tail[tail_index]);
                    assert(ipv6_address_alphabet(tail));
                }
            }
        }
    }
}

pub proof fn ipv6_alphabet_ascii(input: Seq<char>)
    requires
        ipv6_address_alphabet(input),
    ensures
        is_ascii_chars(input),
{
    reveal(ipv6_address_alphabet);
    reveal(is_ascii_chars);
    assert forall|index: int| 0 <= index < input.len() implies
        '\0' <= #[trigger] input[index] <= '\u{7f}' by {
        if ipv6_spec::triptych_is_hex_digit(input[index]) {
            reveal(ipv6_spec::triptych_is_hex_digit);
            reveal(ipv6_spec::triptych_is_digit);
        } else {
            assert(input[index] == ':');
        }
    }
}

pub proof fn ipv6_alphabet_excludes(
    input: Seq<char>,
    character: char,
)
    requires
        ipv6_address_alphabet(input),
        character == '/' || character == '.',
    ensures
        forall|index: int| 0 <= index < input.len() ==>
            #[trigger] input[index] != character,
{
    reveal(ipv6_address_alphabet);
    assert forall|index: int| 0 <= index < input.len() implies
        #[trigger] input[index] != character by {
        if ipv6_spec::triptych_is_hex_digit(input[index]) {
            reveal(ipv6_spec::triptych_is_hex_digit);
            reveal(ipv6_spec::triptych_is_digit);
        } else {
            assert(input[index] == ':');
        }
    }
}

#[verifier::rlimit(125)]
pub proof fn ipv6_full_rep_parses(
    input: Seq<char>,
    start: int,
    index: int,
    end: int,
    items: Seq<char>,
    count: int,
    left: int,
)
    requires
        0 <= start <= index <= end <= input.len(),
        input.subrange(index, end) == items,
        0 <= count < 8,
        0 <= left,
        ipv6_spec::ipv6_rep_0_matches(items, count),
    ensures
        ipaddr_ipv6_state(
            input,
            start,
            index,
            end,
            left,
            0,
            count,
            0,
            false,
            0,
            0,
        ) == Some(
            ipv6_spec::triptych_hex_seq_from(
                items,
                0,
                left,
                0,
            ),
        ),
    decreases items.len(),
{
    reveal(ipv6_spec::ipv6_rep_0_matches);
    let split = choose|split: int|
        0 <= split <= items.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16(
                items.subrange(0, split),
            )
            && (
                (8 <= count + 1
                    && count + 1 <= 8
                    && split == items.len())
                || (count + 1 < 8
                    && split + 1 <= items.len()
                    && items.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_0_matches(
                        items.subrange(
                            split + 1,
                            items.len() as int,
                        ),
                        count + 1,
                    ))
            );
    let hextet = items.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16);
    assert(1 <= hextet.len() <= 4);
    assert forall|position: int| 0 <= position < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[position],
        ) by {}
    assert(
        input.subrange(index, index + hextet.len() as int)
            == hextet
    ) by {
        assert_seqs_equal!(
            input.subrange(index, index + hextet.len() as int)
                == hextet
        );
    }
    ipv6_consume_hextet(
        input,
        start,
        index,
        end,
        left,
        0,
        count,
        0,
        false,
        hextet,
    );
    let hextet_value = ipv6_spec::triptych_hex_seq_of(hextet);
    if split == items.len() {
        assert(count == 7);
        assert(index + split == end);
        assert(items == hextet) by {
            assert_seqs_equal!(items == hextet);
        }
        let empty = Seq::<char>::empty();
        ipv6_hex_seq_hextet_prefix(hextet, empty, left);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                end,
                end,
                left,
                0,
                count,
                0,
                false,
                hextet_value,
                hextet.len() as int,
            ) == Some(left * 65_536 + hextet_value)
        ) by {
            reveal(ipaddr_ipv6_state);
            reveal(crate::model::ipaddr_ipv6_finish);
        }
        assert(
            ipv6_spec::triptych_hex_seq_from(
                items,
                0,
                left,
                0,
            ) == left * 65_536 + hextet_value
        );
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                index,
                end,
                left,
                0,
                count,
                0,
                false,
                0,
                0,
            ) == Some(
                ipv6_spec::triptych_hex_seq_from(
                    items,
                    0,
                    left,
                    0,
                ),
            )
        );
    } else {
        assert(count + 1 < 8);
        let next = index + split + 1;
        let tail =
            items.subrange(split + 1, items.len() as int);
        assert(items.subrange(split, split + 1) == seq![':']);
        assert(items.subrange(split, split + 1)[0] == ':');
        assert(items[split] == ':');
        assert(input[index + split] == ':');
        assert(input.subrange(next, end) == tail) by {
            assert_seqs_equal!(input.subrange(next, end) == tail);
        }
        ipv6_rep0_starts_hex(tail, count + 1);
        assert(input[next] == tail[0]);
        assert(input[next] != ':') by {
            reveal(ipv6_spec::triptych_is_hex_digit);
            reveal(ipv6_spec::triptych_is_digit);
        }
        ipv6_full_rep_parses(
            input,
            start,
            next,
            end,
            tail,
            count + 1,
            left * 65_536 + hextet_value,
        );
        assert(ipaddr_hex_value(input[index + split]) == None) by {
            reveal(ipaddr_hex_value);
        }
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                index + split,
                end,
                left,
                0,
                count,
                0,
                false,
                hextet_value,
                hextet.len() as int,
            ) == ipaddr_ipv6_state(
                input,
                start,
                next,
                end,
                left * 65_536 + hextet_value,
                0,
                count + 1,
                0,
                false,
                0,
                0,
            )
        ) by {
            reveal_with_fuel(ipaddr_ipv6_state, 1);
        }
        let colon_tail = seq![':'] + tail;
        assert(items == hextet + colon_tail) by {
            assert_seqs_equal!(items == hextet + colon_tail);
        }
        ipv6_hex_seq_hextet_prefix(
            hextet,
            colon_tail,
            left,
        );
        assert(
            ipv6_spec::triptych_hex_seq_from(
                colon_tail,
                0,
                left,
                hextet_value,
            ) == ipv6_spec::triptych_hex_seq_from(
                tail,
                0,
                left * 65_536 + hextet_value,
                0,
            )
        ) by {
            reveal_with_fuel(
                ipv6_spec::triptych_hex_seq_from,
                2,
            );
            ipv6_hex_seq_from_concat_suffix(
                seq![':'],
                tail,
                0,
                left * 65_536 + hextet_value,
                0,
            );
        }
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                next,
                end,
                left * 65_536 + hextet_value,
                0,
                count + 1,
                0,
                false,
                0,
                0,
            ) == Some(
                ipv6_spec::triptych_hex_seq_from(
                    tail,
                    0,
                    left * 65_536 + hextet_value,
                    0,
                ),
            )
        );
        assert(
            ipv6_spec::triptych_hex_seq_from(
                items,
                0,
                left,
                0,
            ) == ipv6_spec::triptych_hex_seq_from(
                tail,
                0,
                left * 65_536 + hextet_value,
                0,
            )
        );
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                index,
                end,
                left,
                0,
                count,
                0,
                false,
                0,
                0,
            ) == Some(
                ipv6_spec::triptych_hex_seq_from(
                    items,
                    0,
                    left,
                    0,
                ),
            )
        );
    }
}

#[verifier::rlimit(150)]
pub proof fn ipv6_left_rep_reaches_compression(
    input: Seq<char>,
    start: int,
    index: int,
    end: int,
    items: Seq<char>,
    count: int,
    left: int,
)
    requires
        0 <= start <= index,
        index + items.len() + 2 <= end <= input.len(),
        input.subrange(index, index + items.len() as int) == items,
        input.subrange(
            index + items.len() as int,
            index + items.len() as int + 2,
        ) == seq![':', ':'],
        0 <= count < 7,
        0 <= left,
        ipv6_spec::ipv6_rep_1_matches(items, count),
    ensures
        ipaddr_ipv6_state(
            input,
            start,
            index,
            end,
            left,
            0,
            count,
            0,
            false,
            0,
            0,
        ) == ipaddr_ipv6_state(
            input,
            start,
            index + items.len() as int + 2,
            end,
            ipv6_spec::triptych_hex_seq_from(
                items,
                0,
                left,
                0,
            ),
            0,
            count + ipv6_spec::triptych_segments_of(items),
            0,
            true,
            0,
            0,
        ),
    decreases items.len(),
{
    reveal(ipv6_spec::ipv6_rep_1_matches);
    let split = choose|split: int|
        0 <= split <= items.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16L(
                items.subrange(0, split),
            )
            && (
                (1 <= count + 1
                    && count + 1 <= 7
                    && split == items.len())
                || (count + 1 < 7
                    && split + 1 <= items.len()
                    && items.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_1_matches(
                        items.subrange(
                            split + 1,
                            items.len() as int,
                        ),
                        count + 1,
                    ))
            );
    let hextet = items.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16L);
    assert(1 <= hextet.len() <= 4);
    assert forall|position: int| 0 <= position < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[position],
        ) by {}
    assert(
        input.subrange(index, index + hextet.len() as int)
            == hextet
    ) by {
        assert_seqs_equal!(
            input.subrange(index, index + hextet.len() as int)
                == hextet
        );
    }
    ipv6_consume_hextet(
        input,
        start,
        index,
        end,
        left,
        0,
        count,
        0,
        false,
        hextet,
    );
    let hextet_value = ipv6_spec::triptych_hex_seq_of(hextet);
    if split == items.len() {
        let marker = index + items.len() as int;
        assert(items == hextet) by {
            assert_seqs_equal!(items == hextet);
        }
        assert(input[marker] == ':');
        assert(input[marker + 1] == ':');
        ipv6_hextet_segments(hextet);
        let empty = Seq::<char>::empty();
        ipv6_hex_seq_hextet_prefix(hextet, empty, left);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                marker,
                end,
                left,
                0,
                count,
                0,
                false,
                hextet_value,
                hextet.len() as int,
            ) == ipaddr_ipv6_state(
                input,
                start,
                marker + 2,
                end,
                left * 65_536 + hextet_value,
                0,
                count + 1,
                0,
                true,
                0,
                0,
            )
        ) by {
            reveal_with_fuel(ipaddr_ipv6_state, 1);
        }
    } else {
        let next = index + split + 1;
        let tail =
            items.subrange(split + 1, items.len() as int);
        assert(items.subrange(split, split + 1) == seq![':']);
        assert(items.subrange(split, split + 1)[0] == ':');
        assert(items[split] == ':');
        assert(input[index + split] == ':');
        assert(input.subrange(next, next + tail.len() as int) == tail) by {
            assert_seqs_equal!(
                input.subrange(next, next + tail.len() as int) == tail
            );
        }
        assert(
            input.subrange(
                next + tail.len() as int,
                next + tail.len() as int + 2,
            ) == seq![':', ':']
        ) by {
            assert_seqs_equal!(
                input.subrange(
                    next + tail.len() as int,
                    next + tail.len() as int + 2,
                ) == seq![':', ':']
            );
        }
        ipv6_rep1_starts_hex(tail, count + 1);
        assert(input[next] == tail[0]);
        assert(input[next] != ':') by {
            reveal(ipv6_spec::triptych_is_hex_digit);
            reveal(ipv6_spec::triptych_is_digit);
        }
        ipv6_left_rep_reaches_compression(
            input,
            start,
            next,
            end,
            tail,
            count + 1,
            left * 65_536 + hextet_value,
        );
        assert(ipaddr_hex_value(input[index + split]) == None) by {
            reveal(ipaddr_hex_value);
        }
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                index + split,
                end,
                left,
                0,
                count,
                0,
                false,
                hextet_value,
                hextet.len() as int,
            ) == ipaddr_ipv6_state(
                input,
                start,
                next,
                end,
                left * 65_536 + hextet_value,
                0,
                count + 1,
                0,
                false,
                0,
                0,
            )
        ) by {
            reveal_with_fuel(ipaddr_ipv6_state, 1);
        }
        let colon_tail = seq![':'] + tail;
        assert(items == hextet + colon_tail) by {
            assert_seqs_equal!(items == hextet + colon_tail);
        }
        assert(items == hextet + seq![':'] + tail) by {
            assert_seqs_equal!(
                items == hextet + seq![':'] + tail
            );
        }
        ipv6_hex_seq_hextet_prefix(hextet, colon_tail, left);
        assert(
            ipv6_spec::triptych_hex_seq_from(
                colon_tail,
                0,
                left,
                hextet_value,
            ) == ipv6_spec::triptych_hex_seq_from(
                tail,
                0,
                left * 65_536 + hextet_value,
                0,
            )
        ) by {
            reveal_with_fuel(
                ipv6_spec::triptych_hex_seq_from,
                2,
            );
            ipv6_hex_seq_from_concat_suffix(
                seq![':'],
                tail,
                0,
                left * 65_536 + hextet_value,
                0,
            );
        }
        ipv6_segments_hextet_colon_tail(hextet, tail);
        assert(
            ipv6_spec::triptych_segments_of(items)
                == 1 + ipv6_spec::triptych_segments_of(tail)
        );
    }
}

#[verifier::rlimit(150)]
pub proof fn ipv6_right_rep_parses(
    input: Seq<char>,
    start: int,
    index: int,
    end: int,
    items: Seq<char>,
    left: int,
    right: int,
    left_count: int,
    count: int,
)
    requires
        0 <= start <= index <= end <= input.len(),
        input.subrange(index, end) == items,
        0 <= left,
        0 <= right,
        0 <= left_count < 8,
        0 <= count < 7,
        left_count + count
            + ipv6_spec::triptych_segments_of(items) < 8,
        ipv6_spec::ipv6_rep_2_matches(items, count),
    ensures
        ipaddr_ipv6_state(
            input,
            start,
            index,
            end,
            left,
            right,
            left_count,
            count,
            true,
            0,
            0,
        ) == Some(
            left * crate::model::ipaddr_pow_65536(8 - left_count)
                + ipv6_spec::triptych_hex_seq_from(
                    items,
                    0,
                    right,
                    0,
                ),
        ),
    decreases items.len(),
{
    reveal(ipv6_spec::ipv6_rep_2_matches);
    let split = choose|split: int|
        0 <= split <= items.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16R(
                items.subrange(0, split),
            )
            && (
                (1 <= count + 1
                    && count + 1 <= 7
                    && split == items.len())
                || (count + 1 < 7
                    && split + 1 <= items.len()
                    && items.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_2_matches(
                        items.subrange(
                            split + 1,
                            items.len() as int,
                        ),
                        count + 1,
                    ))
            );
    let hextet = items.subrange(0, split);
    reveal(ipv6_spec::ipv6_is_wf_H16R);
    assert(1 <= hextet.len() <= 4);
    assert forall|position: int| 0 <= position < hextet.len() implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            hextet[position],
        ) by {}
    assert(
        input.subrange(index, index + hextet.len() as int)
            == hextet
    ) by {
        assert_seqs_equal!(
            input.subrange(index, index + hextet.len() as int)
                == hextet
        );
    }
    ipv6_consume_hextet(
        input,
        start,
        index,
        end,
        left,
        right,
        left_count,
        count,
        true,
        hextet,
    );
    let hextet_value = ipv6_spec::triptych_hex_seq_of(hextet);
    if split == items.len() {
        assert(index + split == end);
        assert(items == hextet) by {
            assert_seqs_equal!(items == hextet);
        }
        ipv6_hextet_segments(hextet);
        let empty = Seq::<char>::empty();
        ipv6_hex_seq_hextet_prefix(hextet, empty, right);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                end,
                end,
                left,
                right,
                left_count,
                count,
                true,
                hextet_value,
                hextet.len() as int,
            ) == Some(
                left * crate::model::ipaddr_pow_65536(
                    8 - left_count,
                ) + right * 65_536 + hextet_value,
            )
        ) by {
            reveal(ipaddr_ipv6_state);
            reveal(crate::model::ipaddr_ipv6_finish);
        }
    } else {
        assert(count + 1 < 7);
        let next = index + split + 1;
        let tail =
            items.subrange(split + 1, items.len() as int);
        assert(items.subrange(split, split + 1) == seq![':']);
        assert(items.subrange(split, split + 1)[0] == ':');
        assert(items[split] == ':');
        assert(input[index + split] == ':');
        assert(input.subrange(next, end) == tail) by {
            assert_seqs_equal!(input.subrange(next, end) == tail);
        }
        ipv6_rep2_starts_hex(tail, count + 1);
        assert(input[next] == tail[0]);
        assert(input[next] != ':') by {
            reveal(ipv6_spec::triptych_is_hex_digit);
            reveal(ipv6_spec::triptych_is_digit);
        }
        let colon_tail = seq![':'] + tail;
        assert(items == hextet + colon_tail) by {
            assert_seqs_equal!(items == hextet + colon_tail);
        }
        assert(items == hextet + seq![':'] + tail) by {
            assert_seqs_equal!(
                items == hextet + seq![':'] + tail
            );
        }
        ipv6_segments_hextet_colon_tail(hextet, tail);
        assert(
            ipv6_spec::triptych_segments_of(items)
                == 1 + ipv6_spec::triptych_segments_of(tail)
        );
        ipv6_right_rep_parses(
            input,
            start,
            next,
            end,
            tail,
            left,
            right * 65_536 + hextet_value,
            left_count,
            count + 1,
        );
        assert(ipaddr_hex_value(input[index + split]) == None) by {
            reveal(ipaddr_hex_value);
        }
        assert(
            ipaddr_ipv6_state(
                input,
                start,
                index + split,
                end,
                left,
                right,
                left_count,
                count,
                true,
                hextet_value,
                hextet.len() as int,
            ) == ipaddr_ipv6_state(
                input,
                start,
                next,
                end,
                left,
                right * 65_536 + hextet_value,
                left_count,
                count + 1,
                true,
                0,
                0,
            )
        ) by {
            reveal_with_fuel(ipaddr_ipv6_state, 1);
        }
        ipv6_hex_seq_hextet_prefix(hextet, colon_tail, right);
        assert(
            ipv6_spec::triptych_hex_seq_from(
                colon_tail,
                0,
                right,
                hextet_value,
            ) == ipv6_spec::triptych_hex_seq_from(
                tail,
                0,
                right * 65_536 + hextet_value,
                0,
            )
        ) by {
            reveal_with_fuel(
                ipv6_spec::triptych_hex_seq_from,
                2,
            );
            ipv6_hex_seq_from_concat_suffix(
                seq![':'],
                tail,
                0,
                right * 65_536 + hextet_value,
                0,
            );
        }
    }
}

pub proof fn ipv6_model_pow_matches(exponent: int)
    requires
        0 <= exponent,
    ensures
        crate::model::ipaddr_pow_65536(exponent)
            == ipv6_spec::triptych_int_pow(65_536, exponent),
    decreases exponent,
{
    if exponent == 0 {
        reveal(crate::model::ipaddr_pow_65536);
        reveal_with_fuel(vstd::arithmetic::power::pow, 1);
        reveal(ipv6_spec::triptych_int_pow);
    } else {
        ipv6_model_pow_matches(exponent - 1);
        crate::model::lemma_ipaddr_pow_65536_next(exponent - 1);
        reveal(ipv6_spec::triptych_int_pow);
        lemma_mul_is_commutative(
            crate::model::ipaddr_pow_65536(exponent - 1),
            65_536,
        );
    }
}

pub proof fn ipv6_decimal_nat_matches(
    characters: Seq<char>,
    index: int,
    accumulator: int,
)
    requires
        0 <= index <= characters.len(),
        0 <= accumulator,
        forall|checked: int| index <= checked < characters.len() ==>
            #[trigger] ipv6_spec::triptych_is_digit(
                characters[checked],
            ),
    ensures
        ipaddr_decimal_nat(
            characters,
            index,
            characters.len() as int,
            accumulator,
        ) == Some(
            ipv6_spec::triptych_nat_of_from(
                characters,
                index,
                accumulator,
            ),
        ),
    decreases characters.len() - index,
{
    if index < characters.len() {
        assert(ipv6_spec::triptych_is_digit(characters[index]));
        assert(ipaddr_is_digit(characters[index])) by {
            reveal(ipaddr_is_digit);
            reveal(ipv6_spec::triptych_is_digit);
        }
        assert(
            ipaddr_digit_value(characters[index])
                == if (characters[index] as int)
                    < (ipv6_spec::TRIPTYCH_ZERO as int) {
                    0
                } else {
                    (characters[index] as int)
                        - (ipv6_spec::TRIPTYCH_ZERO as int)
                }
        ) by {
            reveal(ipaddr_digit_value);
            reveal(ipaddr_is_digit);
        }
        assert forall|checked: int|
            index + 1 <= checked < characters.len() implies
                #[trigger] ipv6_spec::triptych_is_digit(
                    characters[checked],
                ) by {}
        ipv6_decimal_nat_matches(
            characters,
            index + 1,
            accumulator * 10 + ipaddr_digit_value(characters[index]),
        );
        reveal(ipaddr_decimal_nat);
        reveal(ipv6_spec::triptych_nat_of_from);
    } else {
        reveal(ipaddr_decimal_nat);
        reveal(ipv6_spec::triptych_nat_of_from);
    }
}

#[verifier::spinoff_prover]
pub proof fn ipv6_prefix_parses(prefix: Seq<char>)
    requires
        1 <= prefix.len() <= 3,
        forall|index: int| 0 <= index < prefix.len() ==>
            #[trigger] ipv6_spec::triptych_is_digit(prefix[index]),
        prefix[0] != '0' || prefix == seq!['0'],
        ipv6_spec::triptych_nat_of(prefix) <= 128,
    ensures
        ipaddr_parse_prefix(prefix, 0, prefix.len() as int, 128)
            == Some(ipv6_spec::triptych_nat_of(prefix)),
{
    ipv6_decimal_nat_matches(prefix, 0, 0);
    reveal(ipv6_spec::triptych_nat_of);
    reveal(ipaddr_parse_prefix);
}

pub proof fn ipv6_rep0_has_colon(input: Seq<char>)
    requires
        ipv6_spec::ipv6_rep_0_matches(input, 0),
    ensures
        exists|index: int|
            0 <= index < input.len() && input[index] == ':',
{
    reveal(ipv6_spec::ipv6_rep_0_matches);
    let split = choose|split: int|
        0 <= split <= input.len()
            && #[trigger] ipv6_spec::ipv6_is_wf_H16(
                input.subrange(0, split),
            )
            && (
                (8 <= 1
                    && 1 <= 8
                    && split == input.len())
                || (1 < 8
                    && split + 1 <= input.len()
                    && input.subrange(split, split + 1)
                        == seq![':']
                    && ipv6_spec::ipv6_rep_0_matches(
                        input.subrange(split + 1, input.len() as int),
                        1,
                    ))
            );
    assert(split < input.len());
    assert(input.subrange(split, split + 1)[0] == ':');
    assert(input[split] == ':');
    assert(exists|index: int|
        0 <= index < input.len() && input[index] == ':') by {
        assert(0 <= split < input.len() && input[split] == ':');
    }
}

pub proof fn ipv6_hex_seq_from_nonnegative(
    input: Seq<char>,
    index: int,
    accumulator: int,
    current: int,
)
    requires
        0 <= index <= input.len(),
        0 <= accumulator,
        0 <= current,
        ipv6_address_alphabet(input),
    ensures
        0 <= ipv6_spec::triptych_hex_seq_from(
            input,
            index,
            accumulator,
            current,
        ),
    decreases input.len() - index,
{
    if index < input.len() {
        reveal(ipv6_address_alphabet);
        if input[index] == ':' {
            ipv6_hex_seq_from_nonnegative(
                input,
                index + 1,
                accumulator * 65_536 + current,
                0,
            );
        } else {
            assert(ipv6_spec::triptych_is_hex_digit(input[index]));
            ipv6_hex_digit_matches(input[index]);
            ipv6_hex_seq_from_nonnegative(
                input,
                index + 1,
                accumulator,
                current * 16
                    + ipv6_spec::triptych_hex_digit_value(
                        input[index],
                    ),
            );
        }
    }
    reveal(ipv6_spec::triptych_hex_seq_from);
}

pub proof fn ipv6_hex_seq_nonnegative(input: Seq<char>)
    requires
        ipv6_address_alphabet(input),
    ensures
        0 <= ipv6_spec::triptych_hex_seq_of(input),
{
    ipv6_hex_seq_from_nonnegative(input, 0, 0, 0);
    reveal(ipv6_spec::triptych_hex_seq_of);
}

pub proof fn ipv6_matches_compressed_elim(
    input: Seq<char>,
    view: ipv6_spec::IPv6View,
)
    requires
        ipv6_spec::ipv6_matches_Compressed(input, view),
    ensures
        exists|left: Seq<char>, right: Seq<char>|
            input == left + seq![':', ':'] + right
                && (
                    left.len() == 0
                        && view.left == seq![]
                    || view.left == left
                        && ipv6_spec::ipv6_matches_Left(
                            left,
                            view,
                        )
                )
                && (
                    right.len() == 0
                        && view.right == seq![]
                    || view.right == right
                        && ipv6_spec::ipv6_matches_Right(
                            right,
                            view,
                        )
                ),
{
    reveal(ipv6_spec::ipv6_matches_Compressed);
    let (left, right) =
        choose|left: Seq<char>, right: Seq<char>|
            input == left + seq!['\u{3a}', '\u{3a}'] + right
                && (
                    left.len() == 0
                        && view.left == seq![]
                    || view.left == left
                        && ipv6_spec::ipv6_matches_Left(left, view)
                )
                && (
                    right.len() == 0
                        && view.right == seq![]
                    || view.right == right
                        && ipv6_spec::ipv6_matches_Right(right, view)
                );
    assert(
        input == left + seq![':', ':'] + right
            && (
                left.len() == 0
                    && view.left == seq![]
                || view.left == left
                    && ipv6_spec::ipv6_matches_Left(left, view)
            )
            && (
                right.len() == 0
                    && view.right == seq![]
                || view.right == right
                    && ipv6_spec::ipv6_matches_Right(right, view)
            )
    );
    assert(exists|candidate_left: Seq<char>, candidate_right: Seq<char>|
        input == candidate_left + seq![':', ':'] + candidate_right
            && (
                candidate_left.len() == 0
                    && view.left == seq![]
                || view.left == candidate_left
                    && ipv6_spec::ipv6_matches_Left(
                        candidate_left,
                        view,
                    )
            )
            && (
                candidate_right.len() == 0
                    && view.right == seq![]
                || view.right == candidate_right
                    && ipv6_spec::ipv6_matches_Right(
                        candidate_right,
                        view,
                    )
            )) by {
        assert(
            input == left + seq![':', ':'] + right
                && (
                    left.len() == 0
                        && view.left == seq![]
                    || view.left == left
                        && ipv6_spec::ipv6_matches_Left(left, view)
                )
                && (
                    right.len() == 0
                        && view.right == seq![]
                    || view.right == right
                        && ipv6_spec::ipv6_matches_Right(right, view)
                )
        );
    }
}

#[verifier::rlimit(250)]
pub proof fn ipv6_generated_address_parses(
    address: Seq<char>,
    view: ipv6_spec::IPv6View,
)
    requires
        ipv6_spec::ipv6_matches_V6Addr(address, view),
        ipv6_spec::ipv6_view_wf_constraints(view),
    ensures
        ipaddr_ipv6_state(
            address,
            0,
            0,
            address.len() as int,
            0,
            0,
            0,
            0,
            false,
            0,
            0,
        ) == Some(
            if view.full == seq![] {
                ipv6_spec::triptych_hex_seq_of(view.left)
                    * ipv6_spec::triptych_int_pow(
                        65_536,
                        8 - ipv6_spec::triptych_segments_of(view.left),
                    )
                    + ipv6_spec::triptych_hex_seq_of(view.right)
            } else {
                ipv6_spec::triptych_hex_seq_of(view.full)
            },
        ),
        is_ascii_chars(address),
        address.len() <= 39,
        forall|index: int| 0 <= index < address.len() ==>
            #[trigger] address[index] != '/',
        forall|index: int| 0 <= index < address.len() ==>
            #[trigger] address[index] != '.',
        exists|index: int|
            0 <= index < address.len() && address[index] == ':',
{
    reveal(ipv6_spec::ipv6_matches_V6Addr);
    reveal(ipv6_spec::ipv6_view_wf_constraints);
    reveal(ipv6_spec::ipv6_wf_constraints);
    let empty = Seq::<char>::empty();
    if exists|full: Seq<char>|
        address == full
            && (view.full == full
                && #[trigger] ipv6_spec::ipv6_matches_Full(
                    full,
                    view,
                ))
            && view.left == seq![]
            && view.right == seq![]
    {
        let full = choose|full: Seq<char>|
            address == full
                && (view.full == full
                    && #[trigger] ipv6_spec::ipv6_matches_Full(
                        full,
                        view,
                    ))
                && view.left == seq![]
                && view.right == seq![];
        reveal(ipv6_spec::ipv6_matches_Full);
        let items = choose|items: Seq<char>|
            full == items
                && #[trigger] ipv6_spec::ipv6_rep_0_matches(
                    items,
                    0,
                );
        assert(items == address);
        assert(
            address.subrange(0, address.len() as int) == items
        ) by {
            assert_seqs_equal!(
                address.subrange(0, address.len() as int) == items
            );
        }
        ipv6_rep0_properties(items, 0);
        ipv6_full_rep_parses(
            address,
            0,
            0,
            address.len() as int,
            items,
            0,
            0,
        );
        ipv6_alphabet_ascii(address);
        ipv6_alphabet_excludes(address, '/');
        ipv6_alphabet_excludes(address, '.');
        ipv6_rep0_has_colon(address);
        reveal(ipv6_spec::triptych_hex_seq_of);
    } else {
        assert(exists|compressed: Seq<char>|
            address == compressed
                && #[trigger] ipv6_spec::ipv6_matches_Compressed(
                    compressed,
                    view,
                )
                && view.full == seq![]);
        let compressed = choose|compressed: Seq<char>|
            address == compressed
                && #[trigger] ipv6_spec::ipv6_matches_Compressed(
                    compressed,
                    view,
                )
                && view.full == seq![];
        assert(address == compressed);
        assert(ipv6_spec::ipv6_matches_Compressed(
            compressed,
            view,
        ));
        assert(view.full == seq![]);
        ipv6_matches_compressed_elim(compressed, view);
        let (left, right) =
            choose|left: Seq<char>, right: Seq<char>|
                compressed == left + seq![':', ':'] + right
                    && (
                        left.len() == 0
                            && view.left == seq![]
                        || view.left == left
                            && ipv6_spec::ipv6_matches_Left(
                                left,
                                view,
                            )
                    )
                    && (
                        right.len() == 0
                            && view.right == seq![]
                        || view.right == right
                            && ipv6_spec::ipv6_matches_Right(
                                right,
                                view,
                            )
                    );
        assert(address == left + seq![':', ':'] + right);
        if left.len() == 0 {
            assert(left == empty) by {
                assert_seqs_equal!(left == empty);
            }
            assert(view.left == empty);
            assert(ipv6_address_alphabet(left)) by {
                reveal(ipv6_address_alphabet);
            }
            reveal(ipv6_spec::triptych_segments_of);
            reveal_with_fuel(ipv6_spec::triptych_hex_seq_of, 1);
            reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 1);
        } else {
            assert(view.left == left);
            reveal(ipv6_spec::ipv6_matches_Left);
            let items = choose|items: Seq<char>|
                left == items
                    && #[trigger] ipv6_spec::ipv6_rep_1_matches(
                        items,
                        0,
                    );
            assert(items == left);
            ipv6_rep1_properties(left, 0);
        }
        if right.len() == 0 {
            assert(right == empty) by {
                assert_seqs_equal!(right == empty);
            }
            assert(view.right == empty);
            assert(ipv6_address_alphabet(right)) by {
                reveal(ipv6_address_alphabet);
            }
            reveal(ipv6_spec::triptych_segments_of);
            reveal_with_fuel(ipv6_spec::triptych_hex_seq_of, 1);
            reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 1);
        } else {
            assert(view.right == right);
            reveal(ipv6_spec::ipv6_matches_Right);
            let items = choose|items: Seq<char>|
                right == items
                    && #[trigger] ipv6_spec::ipv6_rep_2_matches(
                        items,
                        0,
                    );
            assert(items == right);
            ipv6_rep2_properties(right, 0);
        }
        assert(view.full == empty);
        assert(
            ipv6_spec::triptych_segments_of(left)
                + ipv6_spec::triptych_segments_of(right) < 8
        );
        assert(ipv6_address_alphabet(address)) by {
            reveal(ipv6_address_alphabet);
            assert forall|index: int| 0 <= index < address.len() implies
                #[trigger] ipv6_spec::triptych_is_hex_digit(
                    address[index],
                ) || address[index] == ':' by {
                if index < left.len() {
                    assert(address[index] == left[index]);
                    assert(ipv6_address_alphabet(left));
                } else if index < left.len() + 2 {
                    assert(
                        address[index]
                            == seq![':', ':'][index - left.len()]
                    );
                } else {
                    let right_index = index - left.len() - 2;
                    assert(0 <= right_index < right.len());
                    assert(address[index] == right[right_index]);
                    assert(ipv6_address_alphabet(right));
                }
            }
        }
        ipv6_alphabet_ascii(address);
        ipv6_alphabet_excludes(address, '/');
        ipv6_alphabet_excludes(address, '.');
        assert(address[left.len() as int] == ':');
        assert(exists|index: int|
            0 <= index < address.len() && address[index] == ':') by {
            assert(
                0 <= left.len() < address.len()
                    && address[left.len() as int] == ':'
            );
        }
        assert(address.len() <= 39) by {
            if left.len() == 0 && right.len() == 0 {
                assert(address.len() == 2);
            } else if left.len() == 0 {
                assert(
                    right.len()
                        <= 5
                            * ipv6_spec::triptych_segments_of(right)
                            - 1
                );
            } else if right.len() == 0 {
                assert(
                    left.len()
                        <= 5
                            * ipv6_spec::triptych_segments_of(left)
                            - 1
                );
            } else {
                assert(
                    left.len()
                        <= 5
                            * ipv6_spec::triptych_segments_of(left)
                            - 1
                );
                assert(
                    right.len()
                        <= 5
                            * ipv6_spec::triptych_segments_of(right)
                            - 1
                );
            }
        }

        let right_start = left.len() as int + 2;
        assert(
            address.subrange(
                left.len() as int,
                left.len() as int + 2,
            ) == seq![':', ':']
        ) by {
            assert_seqs_equal!(
                address.subrange(
                    left.len() as int,
                    left.len() as int + 2,
                ) == seq![':', ':']
            );
        }
        assert(
            address.subrange(right_start, address.len() as int)
                == right
        ) by {
            assert_seqs_equal!(
                address.subrange(right_start, address.len() as int)
                    == right
            );
        }
        if left.len() == 0 {
            assert(address[0] == ':');
            assert(address[1] == ':');
            assert(
                ipaddr_ipv6_state(
                    address,
                    0,
                    0,
                    address.len() as int,
                    0,
                    0,
                    0,
                    0,
                    false,
                    0,
                    0,
                ) == ipaddr_ipv6_state(
                    address,
                    0,
                    right_start,
                    address.len() as int,
                    0,
                    0,
                    0,
                    0,
                    true,
                    0,
                    0,
                )
            ) by {
                reveal_with_fuel(ipaddr_ipv6_state, 1);
            }
        } else {
            reveal(ipv6_spec::ipv6_matches_Left);
            assert(ipv6_spec::ipv6_rep_1_matches(left, 0));
            assert(
                address.subrange(0, left.len() as int) == left
            ) by {
                assert_seqs_equal!(
                    address.subrange(0, left.len() as int) == left
                );
            }
            ipv6_left_rep_reaches_compression(
                address,
                0,
                0,
                address.len() as int,
                left,
                0,
                0,
            );
            reveal(ipv6_spec::triptych_hex_seq_of);
        }
        let left_value = ipv6_spec::triptych_hex_seq_of(left);
        let left_count = ipv6_spec::triptych_segments_of(left);
        ipv6_hex_seq_nonnegative(left);
        ipv6_hex_seq_nonnegative(right);
        assert(0 <= left_count < 8);
        if right.len() == 0 {
            assert(right_start == address.len());
            assert(
                ipaddr_ipv6_state(
                    address,
                    0,
                    right_start,
                    address.len() as int,
                    left_value,
                    0,
                    left_count,
                    0,
                    true,
                    0,
                    0,
                ) == Some(
                    left_value
                        * crate::model::ipaddr_pow_65536(
                            8 - left_count,
                        ),
                )
            ) by {
                reveal(ipaddr_ipv6_state);
                reveal(crate::model::ipaddr_ipv6_finish);
            }
        } else {
            reveal(ipv6_spec::ipv6_matches_Right);
            assert(ipv6_spec::ipv6_rep_2_matches(right, 0));
            ipv6_right_rep_parses(
                address,
                0,
                right_start,
                address.len() as int,
                right,
                left_value,
                0,
                left_count,
                0,
            );
            reveal(ipv6_spec::triptych_hex_seq_of);
        }
        ipv6_model_pow_matches(8 - left_count);
    }
}

pub open spec fn ipv6_group_wf(group: Seq<char>) -> bool {
    1 <= group.len()
        && group.len() <= 4
        && forall|index: int| 0 <= index < group.len() ==>
            #[trigger] ipv6_spec::triptych_is_hex_digit(group[index])
}

pub open spec fn ipv6_groups_wf(groups: Seq<Seq<char>>) -> bool {
    forall|index: int| 0 <= index < groups.len() ==>
        #[trigger] ipv6_group_wf(groups[index])
}

pub open spec fn ipv6_groups_join_from(
    groups: Seq<Seq<char>>,
    index: int,
) -> Seq<char>
    recommends
        0 <= index <= groups.len(),
    decreases if 0 <= index && index <= groups.len() {
        groups.len() - index
    } else {
        0
    },
{
    if index < 0 || index >= groups.len() {
        Seq::<char>::empty()
    } else if index + 1 == groups.len() {
        groups[index]
    } else {
        groups[index] + seq![':']
            + ipv6_groups_join_from(groups, index + 1)
    }
}

pub open spec fn ipv6_groups_join(
    groups: Seq<Seq<char>>,
) -> Seq<char> {
    ipv6_groups_join_from(groups, 0)
}

pub open spec fn ipv6_groups_value_from(
    groups: Seq<Seq<char>>,
    index: int,
    accumulator: int,
) -> int
    recommends
        0 <= index <= groups.len(),
    decreases if 0 <= index && index <= groups.len() {
        groups.len() - index
    } else {
        0
    },
{
    if index < 0 || index >= groups.len() {
        accumulator
    } else {
        ipv6_groups_value_from(
            groups,
            index + 1,
            accumulator * 65_536
                + ipv6_spec::triptych_hex_seq_of(groups[index]),
        )
    }
}

pub open spec fn ipv6_groups_value(
    groups: Seq<Seq<char>>,
) -> int {
    ipv6_groups_value_from(groups, 0, 0)
}

pub proof fn ipv6_groups_wf_push(
    groups: Seq<Seq<char>>,
    group: Seq<char>,
)
    requires
        ipv6_groups_wf(groups),
        ipv6_group_wf(group),
    ensures
        ipv6_groups_wf(groups.push(group)),
{
    reveal(ipv6_groups_wf);
    assert forall|index: int|
        0 <= index < groups.push(group).len() implies
            #[trigger] ipv6_group_wf(
                groups.push(group)[index],
            ) by {
        if index < groups.len() {
            assert(groups.push(group)[index] == groups[index]);
        } else {
            assert(index == groups.len());
            assert(groups.push(group)[index] == group);
        }
    }
}

pub proof fn ipv6_groups_join_from_push(
    groups: Seq<Seq<char>>,
    group: Seq<char>,
    index: int,
)
    requires
        0 <= index <= groups.len(),
    ensures
        ipv6_groups_join_from(
            groups.push(group),
            index,
        ) == if index == groups.len() {
            group
        } else {
            ipv6_groups_join_from(groups, index)
                + seq![':'] + group
        },
    decreases groups.len() - index,
{
    if index < groups.len() {
        if index + 1 == groups.len() {
            reveal_with_fuel(ipv6_groups_join_from, 2);
        } else {
            ipv6_groups_join_from_push(
                groups,
                group,
                index + 1,
            );
            reveal(ipv6_groups_join_from);
            assert(
                groups[index] + seq![':']
                    + (
                        ipv6_groups_join_from(
                            groups,
                            index + 1,
                        ) + seq![':'] + group
                    )
                    == (
                        groups[index] + seq![':']
                            + ipv6_groups_join_from(
                                groups,
                                index + 1,
                            )
                    ) + seq![':'] + group
            ) by {
                assert_seqs_equal!(
                    groups[index] + seq![':']
                        + (
                            ipv6_groups_join_from(
                                groups,
                                index + 1,
                            ) + seq![':'] + group
                        )
                        == (
                            groups[index] + seq![':']
                                + ipv6_groups_join_from(
                                    groups,
                                    index + 1,
                                )
                        ) + seq![':'] + group
                );
            }
        }
    } else {
        reveal(ipv6_groups_join_from);
    }
}

pub proof fn ipv6_groups_join_push(
    groups: Seq<Seq<char>>,
    group: Seq<char>,
)
    ensures
        ipv6_groups_join(groups.push(group))
            == if groups.len() == 0 {
                group
            } else {
                ipv6_groups_join(groups) + seq![':'] + group
            },
{
    ipv6_groups_join_from_push(groups, group, 0);
    reveal(ipv6_groups_join);
}

pub proof fn ipv6_groups_value_from_push(
    groups: Seq<Seq<char>>,
    group: Seq<char>,
    index: int,
    accumulator: int,
)
    requires
        0 <= index <= groups.len(),
    ensures
        ipv6_groups_value_from(
            groups.push(group),
            index,
            accumulator,
        ) == ipv6_groups_value_from(
            groups,
            index,
            accumulator,
        ) * 65_536
            + ipv6_spec::triptych_hex_seq_of(group),
    decreases groups.len() - index,
{
    if index < groups.len() {
        let next_accumulator =
            accumulator * 65_536
                + ipv6_spec::triptych_hex_seq_of(groups[index]);
        ipv6_groups_value_from_push(
            groups,
            group,
            index + 1,
            next_accumulator,
        );
        assert(
            ipv6_groups_value_from(
                groups.push(group),
                index + 1,
                next_accumulator,
            ) == ipv6_groups_value_from(
                groups,
                index + 1,
                next_accumulator,
            ) * 65_536
                + ipv6_spec::triptych_hex_seq_of(group)
        );
        reveal(ipv6_groups_value_from);
    } else {
        assert(index == groups.len());
        assert(groups.push(group)[index] == group);
        reveal_with_fuel(ipv6_groups_value_from, 2);
    }
}

pub proof fn ipv6_groups_value_push(
    groups: Seq<Seq<char>>,
    group: Seq<char>,
)
    ensures
        ipv6_groups_value(groups.push(group))
            == ipv6_groups_value(groups) * 65_536
                + ipv6_spec::triptych_hex_seq_of(group),
{
    ipv6_groups_value_from_push(groups, group, 0, 0);
    reveal(ipv6_groups_value);
}

pub proof fn ipv6_groups_join_from_subrange(
    groups: Seq<Seq<char>>,
    index: int,
)
    requires
        0 <= index <= groups.len(),
    ensures
        ipv6_groups_join_from(groups, index)
            == ipv6_groups_join(
                groups.subrange(index, groups.len() as int),
            ),
    decreases groups.len() - index,
{
    let suffix =
        groups.subrange(index, groups.len() as int);
    if index == groups.len() {
        assert(suffix.len() == 0);
        reveal(ipv6_groups_join);
        reveal(ipv6_groups_join_from);
    } else if index + 1 == groups.len() {
        assert(suffix.len() == 1);
        assert(suffix[0] == groups[index]);
        reveal(ipv6_groups_join);
        reveal_with_fuel(ipv6_groups_join_from, 2);
    } else {
        let suffix_tail =
            suffix.subrange(1, suffix.len() as int);
        let groups_tail =
            groups.subrange(index + 1, groups.len() as int);
        assert(suffix[0] == groups[index]);
        assert(suffix_tail == groups_tail) by {
            assert_seqs_equal!(suffix_tail == groups_tail);
        }
        ipv6_groups_join_from_subrange(groups, index + 1);
        ipv6_groups_join_from_subrange(suffix, 1);
        assert(
            ipv6_groups_join_from(groups, index + 1)
                == ipv6_groups_join_from(suffix, 1)
        );
        reveal(ipv6_groups_join);
        reveal(ipv6_groups_join_from);
    }
}

pub proof fn ipv6_groups_value_from_subrange(
    groups: Seq<Seq<char>>,
    index: int,
    accumulator: int,
)
    requires
        0 <= index <= groups.len(),
    ensures
        ipv6_groups_value_from(groups, index, accumulator)
            == ipv6_groups_value_from(
                groups.subrange(index, groups.len() as int),
                0,
                accumulator,
            ),
    decreases groups.len() - index,
{
    let suffix =
        groups.subrange(index, groups.len() as int);
    if index < groups.len() {
        assert(suffix[0] == groups[index]);
        let next_accumulator =
            accumulator * 65_536
                + ipv6_spec::triptych_hex_seq_of(groups[index]);
        ipv6_groups_value_from_subrange(
            groups,
            index + 1,
            next_accumulator,
        );
        ipv6_groups_value_from_subrange(
            suffix,
            1,
            next_accumulator,
        );
        assert(
            suffix.subrange(1, suffix.len() as int)
                == groups.subrange(
                    index + 1,
                    groups.len() as int,
                )
        ) by {
            assert_seqs_equal!(
                suffix.subrange(1, suffix.len() as int)
                    == groups.subrange(
                        index + 1,
                        groups.len() as int,
                    )
            );
        }
    }
    reveal(ipv6_groups_value_from);
}

pub proof fn ipv6_groups_join_segments(
    groups: Seq<Seq<char>>,
)
    requires
        ipv6_groups_wf(groups),
        0 < groups.len(),
    ensures
        ipv6_spec::triptych_segments_of(
            ipv6_groups_join(groups),
        ) == groups.len(),
    decreases groups.len(),
{
    reveal(ipv6_groups_wf);
    assert(ipv6_group_wf(groups[0]));
    reveal(ipv6_group_wf);
    if groups.len() == 1 {
        assert(
            ipv6_groups_join(groups) == groups[0]
        ) by {
            reveal(ipv6_groups_join);
            reveal_with_fuel(ipv6_groups_join_from, 2);
        }
        ipv6_hextet_segments(groups[0]);
    } else {
        let tail =
            groups.subrange(1, groups.len() as int);
        assert(0 < tail.len());
        assert(ipv6_groups_wf(tail)) by {
            reveal(ipv6_groups_wf);
            assert forall|index: int| 0 <= index < tail.len() implies
                #[trigger] ipv6_group_wf(tail[index]) by {
                assert(tail[index] == groups[index + 1]);
            }
        }
        ipv6_groups_join_segments(tail);
        assert(
            ipv6_groups_join(groups)
                == groups[0] + seq![':']
                    + ipv6_groups_join(tail)
            ) by {
            reveal(ipv6_groups_join);
            reveal(ipv6_groups_join_from);
            ipv6_groups_join_from_subrange(groups, 1);
        }
        assert(0 < ipv6_groups_join(tail).len()) by {
            reveal(ipv6_groups_join);
            reveal(ipv6_groups_join_from);
        }
        ipv6_segments_hextet_colon_tail(
            groups[0],
            ipv6_groups_join(tail),
        );
    }
}

#[verifier::rlimit(125)]
pub proof fn ipv6_groups_join_value_from(
    groups: Seq<Seq<char>>,
    accumulator: int,
)
    requires
        ipv6_groups_wf(groups),
        0 < groups.len(),
        0 <= accumulator,
    ensures
        ipv6_spec::triptych_hex_seq_from(
            ipv6_groups_join(groups),
            0,
            accumulator,
            0,
        ) == ipv6_groups_value_from(
            groups,
            0,
            accumulator,
        ),
    decreases groups.len(),
{
    reveal(ipv6_groups_wf);
    assert(ipv6_group_wf(groups[0]));
    reveal(ipv6_group_wf);
    if groups.len() == 1 {
        assert(
            ipv6_groups_join(groups) == groups[0]
        ) by {
            reveal(ipv6_groups_join);
            reveal_with_fuel(ipv6_groups_join_from, 2);
        }
        let empty = Seq::<char>::empty();
        ipv6_hex_seq_hextet_prefix(
            groups[0],
            empty,
            accumulator,
        );
        reveal_with_fuel(
            ipv6_spec::triptych_hex_seq_from,
            2,
        );
        reveal_with_fuel(ipv6_groups_value_from, 2);
    } else {
        let tail =
            groups.subrange(1, groups.len() as int);
        assert(0 < tail.len());
        assert(ipv6_groups_wf(tail)) by {
            reveal(ipv6_groups_wf);
            assert forall|index: int|
                0 <= index < tail.len() implies
                    #[trigger] ipv6_group_wf(
                        tail[index],
                    ) by {
                assert(tail[index] == groups[index + 1]);
            }
        }
        let next_accumulator =
            accumulator * 65_536
                + ipv6_spec::triptych_hex_seq_of(groups[0]);
        assert(ipv6_address_alphabet(groups[0])) by {
            reveal(ipv6_address_alphabet);
            assert forall|index: int|
                0 <= index < groups[0].len() implies
                    #[trigger] ipv6_spec::triptych_is_hex_digit(
                        groups[0][index],
                    ) || groups[0][index] == ':' by {
                assert(ipv6_spec::triptych_is_hex_digit(
                    groups[0][index],
                ));
            }
        }
        ipv6_hex_seq_nonnegative(groups[0]);
        assert(0 <= next_accumulator);
        ipv6_groups_join_value_from(tail, next_accumulator);
        assert(
            ipv6_groups_join(groups)
                == groups[0] + seq![':']
                    + ipv6_groups_join(tail)
        ) by {
            reveal(ipv6_groups_join);
            reveal(ipv6_groups_join_from);
            ipv6_groups_join_from_subrange(groups, 1);
        }
        let tail_text = ipv6_groups_join(tail);
        assert(
            ipv6_groups_join(groups)
                == groups[0] + (seq![':'] + tail_text)
        ) by {
            assert_seqs_equal!(
                ipv6_groups_join(groups)
                    == groups[0] + (seq![':'] + tail_text)
            );
        }
        ipv6_hex_seq_hextet_prefix(
            groups[0],
            seq![':'] + tail_text,
            accumulator,
        );
        assert(
            ipv6_spec::triptych_hex_seq_from(
                seq![':'] + tail_text,
                0,
                accumulator,
                ipv6_spec::triptych_hex_seq_of(groups[0]),
            ) == ipv6_spec::triptych_hex_seq_from(
                tail_text,
                0,
                next_accumulator,
                0,
            )
        ) by {
            reveal_with_fuel(
                ipv6_spec::triptych_hex_seq_from,
                2,
            );
            ipv6_hex_seq_from_concat_suffix(
                seq![':'],
                tail_text,
                0,
                next_accumulator,
                0,
            );
        }
        reveal(ipv6_groups_value_from);
        ipv6_groups_value_from_subrange(
            groups,
            1,
            next_accumulator,
        );
        assert(
            ipv6_groups_value_from(
                groups,
                0,
                accumulator,
            ) == ipv6_groups_value_from(
                groups,
                1,
                next_accumulator,
            )
        ) by {
            reveal(ipv6_groups_value_from);
        }
        assert(
            ipv6_groups_value_from(
                groups,
                1,
                next_accumulator,
            ) == ipv6_groups_value_from(
                tail,
                0,
                next_accumulator,
            )
        );
        assert(
            ipv6_spec::triptych_hex_seq_from(
                ipv6_groups_join(groups),
                0,
                accumulator,
                0,
            ) == ipv6_spec::triptych_hex_seq_from(
                tail_text,
                0,
                next_accumulator,
                0,
            )
        );
        assert(
            ipv6_spec::triptych_hex_seq_from(
                tail_text,
                0,
                next_accumulator,
                0,
            ) == ipv6_groups_value_from(
                tail,
                0,
                next_accumulator,
            )
        );
    }
}

pub proof fn ipv6_groups_join_value(
    groups: Seq<Seq<char>>,
)
    requires
        ipv6_groups_wf(groups),
    ensures
        ipv6_spec::triptych_hex_seq_of(
            ipv6_groups_join(groups),
        ) == ipv6_groups_value(groups),
{
    if groups.len() == 0 {
        reveal(ipv6_groups_join);
        reveal(ipv6_groups_join_from);
        reveal(ipv6_groups_value);
        reveal(ipv6_groups_value_from);
        reveal(ipv6_spec::triptych_hex_seq_of);
        reveal(ipv6_spec::triptych_hex_seq_from);
    } else {
        ipv6_groups_join_value_from(groups, 0);
        reveal(ipv6_spec::triptych_hex_seq_of);
        reveal(ipv6_groups_value);
    }
}

pub proof fn ipv6_hex_seq_push_digit(
    characters: Seq<char>,
    digit: char,
)
    requires
        characters.len() <= 3,
        forall|index: int| 0 <= index < characters.len() ==>
            #[trigger] ipv6_spec::triptych_is_hex_digit(
                characters[index],
            ),
        ipv6_spec::triptych_is_hex_digit(digit),
    ensures
        ipv6_spec::triptych_hex_seq_of(characters.push(digit))
            == ipv6_spec::triptych_hex_seq_of(characters) * 16
                + ipv6_spec::triptych_hex_digit_value(digit),
{
    if characters.len() == 0 {
        assert(characters == Seq::<char>::empty()) by {
            assert_seqs_equal!(
                characters == Seq::<char>::empty()
            );
        }
        reveal(ipv6_spec::triptych_hex_seq_of);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
    } else {
        assert(
            characters.push(digit)
                == characters + seq![digit]
        ) by {
            assert_seqs_equal!(
                characters.push(digit)
                    == characters + seq![digit]
            );
        }
        ipv6_hex_seq_hextet_prefix(
            characters,
            seq![digit],
            0,
        );
        reveal(ipv6_spec::triptych_hex_seq_of);
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
    }
}

pub open spec fn ipv6_state_text(
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    compressed: bool,
    current: Seq<char>,
) -> Seq<char> {
    if compressed {
        ipv6_groups_join(left_groups)
            + seq![':', ':']
            + if right_groups.len() == 0 {
                current
            } else {
                ipv6_groups_join(right_groups)
                    + seq![':'] + current
            }
    } else if left_groups.len() == 0 {
        current
    } else {
        ipv6_groups_join(left_groups)
            + seq![':'] + current
    }
}

pub open spec fn ipv6_groups_parse_result(
    address: Seq<char>,
    result: int,
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    compressed: bool,
) -> bool {
    ipv6_groups_wf(left_groups)
        && ipv6_groups_wf(right_groups)
        && if compressed {
            address == ipv6_groups_join(left_groups)
                + seq![':', ':']
                + ipv6_groups_join(right_groups)
                && left_groups.len() + right_groups.len() < 8
                && result
                    == ipv6_groups_value(left_groups)
                        * crate::model::ipaddr_pow_65536(
                            8 - left_groups.len() as int,
                        )
                        + ipv6_groups_value(right_groups)
        } else {
            right_groups.len() == 0
                && left_groups.len() == 8
                && address == ipv6_groups_join(left_groups)
                && result == ipv6_groups_value(left_groups)
        }
}

pub proof fn ipv6_state_text_push_character(
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    compressed: bool,
    current: Seq<char>,
    character: char,
)
    ensures
        ipv6_state_text(
            left_groups,
            right_groups,
            compressed,
            current.push(character),
        ) == ipv6_state_text(
            left_groups,
            right_groups,
            compressed,
            current,
        ).push(character),
{
    reveal(ipv6_state_text);
    assert_seqs_equal!(
        ipv6_state_text(
            left_groups,
            right_groups,
            compressed,
            current.push(character),
        ) == ipv6_state_text(
            left_groups,
            right_groups,
            compressed,
            current,
        ).push(character)
    );
}

pub proof fn ipv6_state_text_single_colon(
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    compressed: bool,
    current: Seq<char>,
)
    requires
        0 < current.len(),
    ensures
        ({
            let next_left =
                if compressed {
                    left_groups
                } else {
                    left_groups.push(current)
                };
            let next_right =
                if compressed {
                    right_groups.push(current)
                } else {
                    right_groups
                };
            ipv6_state_text(
                next_left,
                next_right,
                compressed,
                Seq::<char>::empty(),
            ) == ipv6_state_text(
                left_groups,
                right_groups,
                compressed,
                current,
            ).push(':')
        }),
{
    if compressed {
        ipv6_groups_join_push(right_groups, current);
    } else {
        ipv6_groups_join_push(left_groups, current);
    }
    reveal(ipv6_state_text);
    assert_seqs_equal!(
        ipv6_state_text(
            if compressed {
                left_groups
            } else {
                left_groups.push(current)
            },
            if compressed {
                right_groups.push(current)
            } else {
                right_groups
            },
            compressed,
            Seq::<char>::empty(),
        ) == ipv6_state_text(
            left_groups,
            right_groups,
            compressed,
            current,
        ).push(':')
    );
}

pub proof fn ipv6_state_text_compression(
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    current: Seq<char>,
)
    requires
        0 < current.len(),
        right_groups.len() == 0,
    ensures
        ipv6_state_text(
            left_groups.push(current),
            right_groups,
            true,
            Seq::<char>::empty(),
        ) == ipv6_state_text(
            left_groups,
            right_groups,
            false,
            current,
        ) + seq![':', ':'],
{
    ipv6_groups_join_push(left_groups, current);
    reveal(ipv6_state_text);
    reveal(ipv6_groups_join);
    reveal(ipv6_groups_join_from);
    assert_seqs_equal!(
        ipv6_state_text(
            left_groups.push(current),
            right_groups,
            true,
            Seq::<char>::empty(),
        ) == ipv6_state_text(
            left_groups,
            right_groups,
            false,
            current,
        ) + seq![':', ':']
    );
}

#[verifier::rlimit(250)]
pub proof fn ipv6_state_sound_groups(
    input: Seq<char>,
    start: int,
    index: int,
    end: int,
    left: int,
    right: int,
    left_count: int,
    right_count: int,
    compressed: bool,
    hextet: int,
    digits: int,
    current: Seq<char>,
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    result: int,
)
    requires
        0 <= start <= index <= end <= input.len(),
        0 <= left,
        0 <= right,
        0 <= left_count <= 8,
        0 <= right_count <= 8,
        0 <= hextet <= 65_535,
        0 <= digits <= 4,
        digits <= index - start,
        left_count == left_groups.len(),
        right_count == right_groups.len(),
        left == ipv6_groups_value(left_groups),
        right == ipv6_groups_value(right_groups),
        ipv6_groups_wf(left_groups),
        ipv6_groups_wf(right_groups),
        current.len() == digits,
        current == input.subrange(index - digits, index),
        forall|checked: int| 0 <= checked < current.len() ==>
            #[trigger] ipv6_spec::triptych_is_hex_digit(
                current[checked],
            ),
        hextet == ipv6_spec::triptych_hex_seq_of(current),
        !compressed ==> right_groups.len() == 0,
        current.len() == 0 ==> (
            index < end
                || (compressed && right_groups.len() == 0)
        ),
        index == start ==> (
            left_groups.len() == 0
                && right_groups.len() == 0
                && current.len() == 0
        ),
        ipv6_state_text(
            left_groups,
            right_groups,
            compressed,
            current,
        ) == input.subrange(start, index),
        crate::model::ipaddr_ipv6_state(
            input,
            start,
            index,
            end,
            left,
            right,
            left_count,
            right_count,
            compressed,
            hextet,
            digits,
        ) == Some(result),
    ensures
        exists|final_left: Seq<Seq<char>>,
            final_right: Seq<Seq<char>>,
            final_compressed: bool|
            ipv6_groups_parse_result(
                input.subrange(start, end),
                result,
                final_left,
                final_right,
                final_compressed,
            ),
    decreases end - index,
{
    reveal(crate::model::ipaddr_ipv6_state);
    if index == end {
        let final_left =
            if 0 < digits && !compressed {
                left_groups.push(current)
            } else {
                left_groups
            };
        let final_right =
            if 0 < digits && compressed {
                right_groups.push(current)
            } else {
                right_groups
            };
        if 0 < digits {
            assert(ipv6_group_wf(current)) by {
                reveal(ipv6_group_wf);
            }
            if compressed {
                ipv6_groups_wf_push(right_groups, current);
                ipv6_groups_value_push(right_groups, current);
            } else {
                ipv6_groups_wf_push(left_groups, current);
                ipv6_groups_value_push(left_groups, current);
            }
        }
        assert(ipv6_groups_wf(final_left));
        assert(ipv6_groups_wf(final_right));
        assert(
            input.subrange(start, end)
                == if compressed {
                    ipv6_groups_join(final_left)
                        + seq![':', ':']
                        + ipv6_groups_join(final_right)
                } else {
                    ipv6_groups_join(final_left)
                }
        ) by {
            if 0 < digits {
                if compressed {
                    ipv6_groups_join_push(right_groups, current);
                } else {
                    ipv6_groups_join_push(left_groups, current);
                }
            } else {
                assert(current.len() == 0);
                assert(current == Seq::<char>::empty()) by {
                    assert_seqs_equal!(
                        current == Seq::<char>::empty()
                    );
                }
                assert(compressed);
                assert(right_groups.len() == 0);
            }
            reveal(ipv6_state_text);
            assert_seqs_equal!(
                input.subrange(start, end)
                    == if compressed {
                        ipv6_groups_join(final_left)
                            + seq![':', ':']
                            + ipv6_groups_join(final_right)
                    } else {
                        ipv6_groups_join(final_left)
                    }
            );
        }
        reveal(crate::model::ipaddr_ipv6_finish);
        assert(ipv6_groups_parse_result(
            input.subrange(start, end),
            result,
            final_left,
            final_right,
            compressed,
        )) by {
            reveal(ipv6_groups_parse_result);
            reveal(ipv6_groups_value);
        }
        assert(exists|candidate_left: Seq<Seq<char>>,
            candidate_right: Seq<Seq<char>>,
            candidate_compressed: bool|
            ipv6_groups_parse_result(
                input.subrange(start, end),
                result,
                candidate_left,
                candidate_right,
                candidate_compressed,
            )) by {
            assert(ipv6_groups_parse_result(
                input.subrange(start, end),
                result,
                final_left,
                final_right,
                compressed,
            ));
        }
    } else {
        match ipaddr_hex_value(input[index]) {
            Some(digit) => {
                if digits == 4 {
                    assert(false);
                } else {
                    ipv6_model_hex_digit_matches(
                        input[index],
                        digit,
                    );
                    ipv6_hex_seq_push_digit(
                        current,
                        input[index],
                    );
                    let next_current =
                        current.push(input[index]);
                    assert(0 <= index - digits);
                    assert(
                        next_current
                            == input.subrange(
                                index - digits,
                                index + 1,
                        )
                    ) by {
                        assert(
                            input.subrange(
                                index - digits,
                                index + 1,
                            ) == input.subrange(
                                index - digits,
                                index,
                            ).push(input[index])
                        ) by {
                            assert_seqs_equal!(
                                input.subrange(
                                    index - digits,
                                    index + 1,
                                ) == input.subrange(
                                    index - digits,
                                    index,
                                ).push(input[index])
                            );
                        }
                        assert_seqs_equal!(
                            next_current
                                == input.subrange(
                                    index - digits,
                                    index + 1,
                            )
                        );
                    }
                    ipv6_state_text_push_character(
                        left_groups,
                        right_groups,
                        compressed,
                        current,
                        input[index],
                    );
                    assert(
                        input.subrange(start, index + 1)
                            == input.subrange(start, index).push(
                                input[index],
                            )
                    ) by {
                        assert_seqs_equal!(
                            input.subrange(start, index + 1)
                                == input.subrange(start, index).push(
                                    input[index],
                                )
                        );
                    }
                    assert(
                        ipv6_state_text(
                            left_groups,
                            right_groups,
                            compressed,
                            next_current,
                        ) == input.subrange(start, index + 1)
                    );
                    assert forall|checked: int|
                        0 <= checked < next_current.len() implies
                            #[trigger] ipv6_spec::triptych_is_hex_digit(
                                next_current[checked],
                            ) by {
                        if checked < current.len() {
                            assert(
                                next_current[checked]
                                    == current[checked]
                            );
                        } else {
                            assert(checked == current.len());
                            assert(
                                next_current[checked] == input[index]
                            );
                        }
                    }
                    ipv6_state_sound_groups(
                        input,
                        start,
                        index + 1,
                        end,
                        left,
                        right,
                        left_count,
                        right_count,
                        compressed,
                        hextet * 16 + digit,
                        digits + 1,
                        next_current,
                        left_groups,
                        right_groups,
                        result,
                    );
                }
            },
            None => {
                if input[index] != ':' {
                    assert(false);
                } else if digits == 0 {
                    if index == start
                        && index + 1 < end
                        && input[index + 1] == ':'
                        && !compressed
                    {
                        let empty = Seq::<char>::empty();
                        assert(left_groups.len() == 0);
                        assert(right_groups.len() == 0);
                        assert(left_groups == Seq::<Seq<char>>::empty()) by {
                            assert_seqs_equal!(
                                left_groups
                                    == Seq::<Seq<char>>::empty()
                            );
                        }
                        assert(right_groups == Seq::<Seq<char>>::empty()) by {
                            assert_seqs_equal!(
                                right_groups
                                    == Seq::<Seq<char>>::empty()
                            );
                        }
                        assert(
                            ipv6_state_text(
                                left_groups,
                                right_groups,
                                true,
                                empty,
                            ) == input.subrange(start, index + 2)
                        ) by {
                            reveal(ipv6_state_text);
                            reveal(ipv6_groups_join);
                            reveal(ipv6_groups_join_from);
                            assert_seqs_equal!(
                                ipv6_state_text(
                                    left_groups,
                                    right_groups,
                                    true,
                                    empty,
                                ) == input.subrange(
                                    start,
                                    index + 2,
                                )
                            );
                        }
                        assert(
                            empty
                                == input.subrange(
                                    index + 2,
                                    index + 2,
                                )
                        ) by {
                            assert_seqs_equal!(
                                empty
                                    == input.subrange(
                                        index + 2,
                                        index + 2,
                                    )
                            );
                        }
                        ipv6_state_sound_groups(
                            input,
                            start,
                            index + 2,
                            end,
                            left,
                            right,
                            left_count,
                            right_count,
                            true,
                            0,
                            0,
                            empty,
                            left_groups,
                            right_groups,
                            result,
                        );
                    } else {
                        assert(false);
                    }
                } else {
                    assert(ipv6_group_wf(current)) by {
                        reveal(ipv6_group_wf);
                    }
                    ipv6_hex_seq_nonnegative(current);
                    let next_left_groups =
                        if compressed {
                            left_groups
                        } else {
                            left_groups.push(current)
                        };
                    let next_right_groups =
                        if compressed {
                            right_groups.push(current)
                        } else {
                            right_groups
                        };
                    let next_left =
                        if compressed {
                            left
                        } else {
                            left * 65_536 + hextet
                        };
                    let next_right =
                        if compressed {
                            right * 65_536 + hextet
                        } else {
                            right
                        };
                    let next_left_count =
                        if compressed {
                            left_count
                        } else {
                            left_count + 1
                        };
                    let next_right_count =
                        if compressed {
                            right_count + 1
                        } else {
                            right_count
                        };
                    if compressed {
                        ipv6_groups_wf_push(
                            right_groups,
                            current,
                        );
                        ipv6_groups_value_push(
                            right_groups,
                            current,
                        );
                    } else {
                        ipv6_groups_wf_push(
                            left_groups,
                            current,
                        );
                        ipv6_groups_value_push(
                            left_groups,
                            current,
                        );
                    }
                    assert(
                        next_left
                            == ipv6_groups_value(next_left_groups)
                    );
                    assert(
                        next_right
                            == ipv6_groups_value(next_right_groups)
                    );
                    assert(0 <= next_left);
                    assert(0 <= next_right);
                    if next_left_count > 8
                        || next_right_count > 8
                    {
                        assert(false);
                    } else if index + 1 < end
                        && input[index + 1] == ':'
                    {
                        if compressed {
                            assert(false);
                        } else {
                            let empty = Seq::<char>::empty();
                            ipv6_state_text_compression(
                                left_groups,
                                right_groups,
                                current,
                            );
                            assert(
                                input.subrange(start, index + 2)
                                    == input.subrange(start, index)
                                        + seq![':', ':']
                            ) by {
                                assert_seqs_equal!(
                                    input.subrange(start, index + 2)
                                        == input.subrange(start, index)
                                            + seq![':', ':']
                                );
                            }
                            assert(
                                ipv6_state_text(
                                    next_left_groups,
                                    next_right_groups,
                                    true,
                                    empty,
                                ) == input.subrange(
                                    start,
                                    index + 2,
                                )
                            );
                            assert(
                                empty
                                    == input.subrange(
                                        index + 2,
                                        index + 2,
                                    )
                            ) by {
                                assert_seqs_equal!(
                                    empty
                                        == input.subrange(
                                            index + 2,
                                            index + 2,
                                        )
                                );
                            }
                            ipv6_state_sound_groups(
                                input,
                                start,
                                index + 2,
                                end,
                                next_left,
                                next_right,
                                next_left_count,
                                next_right_count,
                                true,
                                0,
                                0,
                                empty,
                                next_left_groups,
                                next_right_groups,
                                result,
                            );
                        }
                    } else if index + 1 == end {
                        assert(false);
                    } else {
                        let empty = Seq::<char>::empty();
                        ipv6_state_text_single_colon(
                            left_groups,
                            right_groups,
                            compressed,
                            current,
                        );
                        assert(
                            input.subrange(start, index + 1)
                                == input.subrange(start, index).push(':')
                        ) by {
                            assert(input[index] == ':');
                            assert_seqs_equal!(
                                input.subrange(start, index + 1)
                                    == input.subrange(start, index).push(':')
                            );
                        }
                        assert(
                            ipv6_state_text(
                                next_left_groups,
                                next_right_groups,
                                compressed,
                                empty,
                            ) == input.subrange(
                                start,
                                index + 1,
                            )
                        );
                        assert(
                            empty
                                == input.subrange(
                                    index + 1,
                                    index + 1,
                                )
                        ) by {
                            assert_seqs_equal!(
                                empty
                                    == input.subrange(
                                        index + 1,
                                        index + 1,
                                    )
                            );
                        }
                        ipv6_state_sound_groups(
                            input,
                            start,
                            index + 1,
                            end,
                            next_left,
                            next_right,
                            next_left_count,
                            next_right_count,
                            compressed,
                            0,
                            0,
                            empty,
                            next_left_groups,
                            next_right_groups,
                            result,
                        );
                    }
                }
            },
        }
    }
}

pub proof fn ipv6_group_wf_matches_h16(group: Seq<char>)
    requires
        ipv6_group_wf(group),
    ensures
        ipv6_spec::ipv6_is_wf_H16(group),
        ipv6_spec::ipv6_is_wf_H16L(group),
        ipv6_spec::ipv6_is_wf_H16R(group),
{
    reveal(ipv6_group_wf);
    reveal(ipv6_spec::ipv6_is_wf_H16);
    reveal(ipv6_spec::ipv6_is_wf_H16L);
    reveal(ipv6_spec::ipv6_is_wf_H16R);
}

pub proof fn ipv6_groups_rep0_matches(
    groups: Seq<Seq<char>>,
    count: int,
)
    requires
        ipv6_groups_wf(groups),
        0 < groups.len(),
        0 <= count,
        count + groups.len() == 8,
    ensures
        ipv6_spec::ipv6_rep_0_matches(
            ipv6_groups_join(groups),
            count,
        ),
    decreases groups.len(),
{
    reveal(ipv6_groups_wf);
    ipv6_group_wf_matches_h16(groups[0]);
    if groups.len() == 1 {
        assert(count == 7);
        reveal(ipv6_groups_join);
        reveal_with_fuel(ipv6_groups_join_from, 2);
        reveal(ipv6_spec::ipv6_rep_0_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_groups_join(groups).len()
                && ipv6_spec::ipv6_is_wf_H16(
                    ipv6_groups_join(groups).subrange(0, split),
                )
                && 8 <= count + 1
                && count + 1 <= 8
                && split == ipv6_groups_join(groups).len()) by {
            let split = groups[0].len() as int;
            assert(
                ipv6_groups_join(groups).subrange(0, split)
                    == groups[0]
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(0, split)
                        == groups[0]
                );
            }
        }
    } else {
        let tail =
            groups.subrange(1, groups.len() as int);
        assert(0 < tail.len());
        assert(ipv6_groups_wf(tail)) by {
            reveal(ipv6_groups_wf);
            assert forall|index: int|
                0 <= index < tail.len() implies
                    #[trigger] ipv6_group_wf(tail[index]) by {
                assert(tail[index] == groups[index + 1]);
            }
        }
        ipv6_groups_rep0_matches(tail, count + 1);
        ipv6_groups_join_from_subrange(groups, 1);
        assert(
            ipv6_groups_join(groups)
                == groups[0] + seq![':']
                    + ipv6_groups_join(tail)
        ) by {
            reveal(ipv6_groups_join);
            reveal(ipv6_groups_join_from);
        }
        reveal(ipv6_spec::ipv6_rep_0_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_groups_join(groups).len()
                && ipv6_spec::ipv6_is_wf_H16(
                    ipv6_groups_join(groups).subrange(0, split),
                )
                && count + 1 < 8
                && split + 1 <= ipv6_groups_join(groups).len()
                && ipv6_groups_join(groups).subrange(
                    split,
                    split + 1,
                ) == seq![':']
                && ipv6_spec::ipv6_rep_0_matches(
                    ipv6_groups_join(groups).subrange(
                        split + 1,
                        ipv6_groups_join(groups).len() as int,
                    ),
                    count + 1,
                )) by {
            let split = groups[0].len() as int;
            assert(
                ipv6_groups_join(groups).subrange(0, split)
                    == groups[0]
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(0, split)
                        == groups[0]
                );
            }
            assert(
                ipv6_groups_join(groups).subrange(
                    split,
                    split + 1,
                ) == seq![':']
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(
                        split,
                        split + 1,
                    ) == seq![':']
                );
            }
            assert(
                ipv6_groups_join(groups).subrange(
                    split + 1,
                    ipv6_groups_join(groups).len() as int,
                ) == ipv6_groups_join(tail)
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(
                        split + 1,
                        ipv6_groups_join(groups).len() as int,
                    ) == ipv6_groups_join(tail)
                );
            }
        }
    }
}

pub proof fn ipv6_groups_rep1_matches(
    groups: Seq<Seq<char>>,
    count: int,
)
    requires
        ipv6_groups_wf(groups),
        0 < groups.len(),
        0 <= count,
        count + groups.len() <= 7,
    ensures
        ipv6_spec::ipv6_rep_1_matches(
            ipv6_groups_join(groups),
            count,
        ),
    decreases groups.len(),
{
    reveal(ipv6_groups_wf);
    ipv6_group_wf_matches_h16(groups[0]);
    if groups.len() == 1 {
        reveal(ipv6_groups_join);
        reveal_with_fuel(ipv6_groups_join_from, 2);
        reveal(ipv6_spec::ipv6_rep_1_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_groups_join(groups).len()
                && ipv6_spec::ipv6_is_wf_H16L(
                    ipv6_groups_join(groups).subrange(0, split),
                )
                && 1 <= count + 1
                && count + 1 <= 7
                && split == ipv6_groups_join(groups).len()) by {
            let split = groups[0].len() as int;
            assert(
                ipv6_groups_join(groups).subrange(0, split)
                    == groups[0]
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(0, split)
                        == groups[0]
                );
            }
        }
    } else {
        let tail =
            groups.subrange(1, groups.len() as int);
        assert(0 < tail.len());
        assert(ipv6_groups_wf(tail)) by {
            reveal(ipv6_groups_wf);
            assert forall|index: int|
                0 <= index < tail.len() implies
                    #[trigger] ipv6_group_wf(tail[index]) by {
                assert(tail[index] == groups[index + 1]);
            }
        }
        ipv6_groups_rep1_matches(tail, count + 1);
        ipv6_groups_join_from_subrange(groups, 1);
        assert(
            ipv6_groups_join(groups)
                == groups[0] + seq![':']
                    + ipv6_groups_join(tail)
        ) by {
            reveal(ipv6_groups_join);
            reveal(ipv6_groups_join_from);
        }
        reveal(ipv6_spec::ipv6_rep_1_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_groups_join(groups).len()
                && ipv6_spec::ipv6_is_wf_H16L(
                    ipv6_groups_join(groups).subrange(0, split),
                )
                && count + 1 < 7
                && split + 1 <= ipv6_groups_join(groups).len()
                && ipv6_groups_join(groups).subrange(
                    split,
                    split + 1,
                ) == seq![':']
                && ipv6_spec::ipv6_rep_1_matches(
                    ipv6_groups_join(groups).subrange(
                        split + 1,
                        ipv6_groups_join(groups).len() as int,
                    ),
                    count + 1,
                )) by {
            let split = groups[0].len() as int;
            assert(
                ipv6_groups_join(groups).subrange(0, split)
                    == groups[0]
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(0, split)
                        == groups[0]
                );
            }
            assert(
                ipv6_groups_join(groups).subrange(
                    split,
                    split + 1,
                ) == seq![':']
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(
                        split,
                        split + 1,
                    ) == seq![':']
                );
            }
            assert(
                ipv6_groups_join(groups).subrange(
                    split + 1,
                    ipv6_groups_join(groups).len() as int,
                ) == ipv6_groups_join(tail)
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(
                        split + 1,
                        ipv6_groups_join(groups).len() as int,
                    ) == ipv6_groups_join(tail)
                );
            }
        }
    }
}

pub proof fn ipv6_groups_rep2_matches(
    groups: Seq<Seq<char>>,
    count: int,
)
    requires
        ipv6_groups_wf(groups),
        0 < groups.len(),
        0 <= count,
        count + groups.len() <= 7,
    ensures
        ipv6_spec::ipv6_rep_2_matches(
            ipv6_groups_join(groups),
            count,
        ),
    decreases groups.len(),
{
    reveal(ipv6_groups_wf);
    ipv6_group_wf_matches_h16(groups[0]);
    if groups.len() == 1 {
        reveal(ipv6_groups_join);
        reveal_with_fuel(ipv6_groups_join_from, 2);
        reveal(ipv6_spec::ipv6_rep_2_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_groups_join(groups).len()
                && ipv6_spec::ipv6_is_wf_H16R(
                    ipv6_groups_join(groups).subrange(0, split),
                )
                && 1 <= count + 1
                && count + 1 <= 7
                && split == ipv6_groups_join(groups).len()) by {
            let split = groups[0].len() as int;
            assert(
                ipv6_groups_join(groups).subrange(0, split)
                    == groups[0]
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(0, split)
                        == groups[0]
                );
            }
        }
    } else {
        let tail =
            groups.subrange(1, groups.len() as int);
        assert(0 < tail.len());
        assert(ipv6_groups_wf(tail)) by {
            reveal(ipv6_groups_wf);
            assert forall|index: int|
                0 <= index < tail.len() implies
                    #[trigger] ipv6_group_wf(tail[index]) by {
                assert(tail[index] == groups[index + 1]);
            }
        }
        ipv6_groups_rep2_matches(tail, count + 1);
        ipv6_groups_join_from_subrange(groups, 1);
        assert(
            ipv6_groups_join(groups)
                == groups[0] + seq![':']
                    + ipv6_groups_join(tail)
        ) by {
            reveal(ipv6_groups_join);
            reveal(ipv6_groups_join_from);
        }
        reveal(ipv6_spec::ipv6_rep_2_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_groups_join(groups).len()
                && ipv6_spec::ipv6_is_wf_H16R(
                    ipv6_groups_join(groups).subrange(0, split),
                )
                && count + 1 < 7
                && split + 1 <= ipv6_groups_join(groups).len()
                && ipv6_groups_join(groups).subrange(
                    split,
                    split + 1,
                ) == seq![':']
                && ipv6_spec::ipv6_rep_2_matches(
                    ipv6_groups_join(groups).subrange(
                        split + 1,
                        ipv6_groups_join(groups).len() as int,
                    ),
                    count + 1,
                )) by {
            let split = groups[0].len() as int;
            assert(
                ipv6_groups_join(groups).subrange(0, split)
                    == groups[0]
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(0, split)
                        == groups[0]
                );
            }
            assert(
                ipv6_groups_join(groups).subrange(
                    split,
                    split + 1,
                ) == seq![':']
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(
                        split,
                        split + 1,
                    ) == seq![':']
                );
            }
            assert(
                ipv6_groups_join(groups).subrange(
                    split + 1,
                    ipv6_groups_join(groups).len() as int,
                ) == ipv6_groups_join(tail)
            ) by {
                assert_seqs_equal!(
                    ipv6_groups_join(groups).subrange(
                        split + 1,
                        ipv6_groups_join(groups).len() as int,
                    ) == ipv6_groups_join(tail)
                );
            }
        }
    }
}

pub proof fn ipv6_group_value_bounds(group: Seq<char>)
    requires
        ipv6_group_wf(group),
    ensures
        0 <= ipv6_spec::triptych_hex_seq_of(group) <= 65_535,
{
    reveal(ipv6_group_wf);
    assert(
        group.subrange(0, group.len() as int) == group
    ) by {
        assert_seqs_equal!(
            group.subrange(0, group.len() as int) == group
        );
    }
    ipv6_consume_hextet(
        group,
        0,
        0,
        group.len() as int,
        0,
        0,
        0,
        0,
        false,
        group,
    );
}

pub proof fn ipv6_groups_value_fits(
    groups: Seq<Seq<char>>,
)
    requires
        ipv6_groups_wf(groups),
    ensures
        0 <= ipv6_groups_value(groups),
        ipv6_groups_value(groups)
            < crate::model::ipaddr_pow_65536(
                groups.len() as int,
            ),
    decreases groups.len(),
{
    if groups.len() == 0 {
        reveal(ipv6_groups_value);
        reveal(ipv6_groups_value_from);
        reveal(crate::model::ipaddr_pow_65536);
        reveal_with_fuel(vstd::arithmetic::power::pow, 1);
    } else {
        let prefix =
            groups.subrange(0, groups.len() as int - 1);
        let group = groups[groups.len() as int - 1];
        assert(groups == prefix.push(group)) by {
            assert_seqs_equal!(groups == prefix.push(group));
        }
        assert(ipv6_groups_wf(prefix)) by {
            reveal(ipv6_groups_wf);
            assert forall|index: int|
                0 <= index < prefix.len() implies
                    #[trigger] ipv6_group_wf(prefix[index]) by {
                assert(prefix[index] == groups[index]);
            }
        }
        assert(ipv6_group_wf(group)) by {
            reveal(ipv6_groups_wf);
        }
        ipv6_groups_value_fits(prefix);
        ipv6_group_value_bounds(group);
        ipv6_groups_value_push(prefix, group);
        crate::model::lemma_ipaddr_pow_65536_next(
            prefix.len() as int,
        );
        let prefix_value = ipv6_groups_value(prefix);
        let group_value =
            ipv6_spec::triptych_hex_seq_of(group);
        let prefix_limit =
            crate::model::ipaddr_pow_65536(
                prefix.len() as int,
            );
        assert(
            prefix_value * 65_536 + group_value
                < (prefix_value + 1) * 65_536
        );
        assert(prefix_value + 1 <= prefix_limit);
        lemma_mul_left_inequality(
            65_536,
            prefix_value + 1,
            prefix_limit,
        );
        lemma_mul_is_commutative(
            65_536,
            prefix_value + 1,
        );
        lemma_mul_is_commutative(65_536, prefix_limit);
    }
}

pub proof fn ipv6_groups_value_accumulator_fits(
    groups: Seq<Seq<char>>,
)
    requires
        ipv6_groups_wf(groups),
        groups.len() <= 8,
    ensures
        crate::model::ipaddr_accumulator_fits(
            ipv6_groups_value(groups),
            groups.len() as int,
        ),
{
    ipv6_groups_value_fits(groups);
    reveal(crate::model::ipaddr_accumulator_fits);
    reveal(crate::model::ipaddr_pow_65536);
    reveal_with_fuel(vstd::arithmetic::power::pow, 9);
    if groups.len() == 0 {
    } else if groups.len() == 1 {
    } else if groups.len() == 2 {
    } else if groups.len() == 3 {
    } else if groups.len() == 4 {
    } else if groups.len() == 5 {
    } else if groups.len() == 6 {
    } else if groups.len() == 7 {
    } else {
        assert(groups.len() == 8);
    }
}

pub proof fn ipv6_groups_parse_result_bounds(
    address: Seq<char>,
    result: int,
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    compressed: bool,
)
    requires
        ipv6_groups_parse_result(
            address,
            result,
            left_groups,
            right_groups,
            compressed,
        ),
    ensures
        0 <= result < ipv6_address_space(),
{
    reveal(ipv6_groups_parse_result);
    ipv6_groups_value_accumulator_fits(left_groups);
    ipv6_groups_value_accumulator_fits(right_groups);
    reveal(crate::model::ipaddr_accumulator_fits);
    assert(0 <= ipv6_groups_value(left_groups));
    assert(0 <= ipv6_groups_value(right_groups));
    if compressed {
        crate::model::lemma_ipaddr_pow_65536_positive(
            8 - left_groups.len() as int,
        );
        assert(0 <= result);
        crate::model::lemma_ipaddr_ipv6_join_fits(
            ipv6_groups_value(left_groups),
            ipv6_groups_value(right_groups),
            left_groups.len() as int,
            right_groups.len() as int,
        );
    } else {
        ipv6_groups_value_fits(left_groups);
        assert(0 <= result);
        crate::model::lemma_ipaddr_pow_65536_eight();
    }
    reveal(ipv6_address_space);
}

#[verifier::rlimit(300)]
pub proof fn ipv6_groups_build_valid_view(
    input: Seq<char>,
    address: Seq<char>,
    prefix: Seq<char>,
    address_value: int,
    prefix_value: int,
    left_groups: Seq<Seq<char>>,
    right_groups: Seq<Seq<char>>,
    compressed: bool,
)
    requires
        ipv6_groups_parse_result(
            address,
            address_value,
            left_groups,
            right_groups,
            compressed,
        ),
        input == address + if prefix.len() == 0 {
            Seq::<char>::empty()
        } else {
            seq!['/'] + prefix
        },
        prefix.len() == 0 || (
            1 <= prefix.len() <= 3
                && (forall|index: int| 0 <= index < prefix.len() ==>
                    #[trigger] ipv6_spec::triptych_is_digit(
                        prefix[index],
                    ))
                && (prefix[0] != '0' || prefix == seq!['0'])
                && 0 <= ipv6_spec::triptych_nat_of(prefix) <= 128
        ),
        prefix_value == if prefix.len() == 0 {
            128
        } else {
            ipv6_spec::triptych_nat_of(prefix)
        },
    ensures
        crate::ipv6::contract::ipv6_matches_result(
            input,
            address_value * 129 + prefix_value,
        ),
        ipv6_spec::ipv6_is_valid(input),
{
    reveal(ipv6_groups_parse_result);
    let empty = Seq::<char>::empty();
    let left_text = ipv6_groups_join(left_groups);
    let right_text = ipv6_groups_join(right_groups);
    let view = ipv6_spec::IPv6View {
        input,
        full: if compressed { empty } else { address },
        left: if compressed { left_text } else { empty },
        right: if compressed { right_text } else { empty },
        prefix,
    };
    if compressed {
        if left_groups.len() == 0 {
            assert(left_groups == Seq::<Seq<char>>::empty()) by {
                assert_seqs_equal!(
                    left_groups == Seq::<Seq<char>>::empty()
                );
            }
            assert(left_text == empty) by {
                reveal(ipv6_groups_join);
                reveal(ipv6_groups_join_from);
            }
        } else {
            ipv6_groups_rep1_matches(left_groups, 0);
            assert(ipv6_spec::ipv6_matches_Left(
                left_text,
                view,
            )) by {
                reveal(ipv6_spec::ipv6_matches_Left);
            }
            assert(ipv6_spec::ipv6_is_wf_Left(left_text)) by {
                reveal(ipv6_spec::ipv6_is_wf_Left);
            }
        }
        if right_groups.len() == 0 {
            assert(right_groups == Seq::<Seq<char>>::empty()) by {
                assert_seqs_equal!(
                    right_groups == Seq::<Seq<char>>::empty()
                );
            }
            assert(right_text == empty) by {
                reveal(ipv6_groups_join);
                reveal(ipv6_groups_join_from);
            }
        } else {
            ipv6_groups_rep2_matches(right_groups, 0);
            assert(ipv6_spec::ipv6_matches_Right(
                right_text,
                view,
            )) by {
                reveal(ipv6_spec::ipv6_matches_Right);
            }
            assert(ipv6_spec::ipv6_is_wf_Right(right_text)) by {
                reveal(ipv6_spec::ipv6_is_wf_Right);
            }
        }
        assert(ipv6_spec::ipv6_matches_Compressed(
            address,
            view,
        )) by {
            reveal(ipv6_spec::ipv6_matches_Compressed);
        }
        assert(ipv6_spec::ipv6_is_wf_Compressed(address)) by {
            reveal(ipv6_spec::ipv6_is_wf_Compressed);
        }
        assert(ipv6_spec::ipv6_matches_V6Addr(
            address,
            view,
        )) by {
            reveal(ipv6_spec::ipv6_matches_V6Addr);
        }
        assert(ipv6_spec::ipv6_is_wf_V6Addr(address)) by {
            reveal(ipv6_spec::ipv6_is_wf_V6Addr);
        }
    } else {
        ipv6_groups_rep0_matches(left_groups, 0);
        assert(ipv6_spec::ipv6_matches_Full(
            address,
            view,
        )) by {
            reveal(ipv6_spec::ipv6_matches_Full);
        }
        assert(ipv6_spec::ipv6_is_wf_Full(address)) by {
            reveal(ipv6_spec::ipv6_is_wf_Full);
        }
        assert(ipv6_spec::ipv6_matches_V6Addr(
            address,
            view,
        )) by {
            reveal(ipv6_spec::ipv6_matches_V6Addr);
        }
        assert(ipv6_spec::ipv6_is_wf_V6Addr(address)) by {
            reveal(ipv6_spec::ipv6_is_wf_V6Addr);
        }
    }
    if prefix.len() == 0 {
        assert(prefix == empty) by {
            assert_seqs_equal!(prefix == empty);
        }
        assert(ipv6_spec::ipv6_matches_V6Net(input, view)) by {
            reveal(ipv6_spec::ipv6_matches_V6Net);
        }
        assert(ipv6_spec::ipv6_is_wf_V6Net(input)) by {
            reveal(ipv6_spec::ipv6_is_wf_V6Net);
        }
    } else {
        assert(input == address + seq!['/'] + prefix) by {
            assert_seqs_equal!(
                input == address + seq!['/'] + prefix
            );
        }
        assert(ipv6_spec::ipv6_matches_Prefix(
            prefix,
            view,
        )) by {
            reveal(ipv6_spec::ipv6_matches_Prefix);
        }
        assert(ipv6_spec::ipv6_is_wf_Prefix(prefix)) by {
            reveal(ipv6_spec::ipv6_is_wf_Prefix);
        }
        assert(ipv6_spec::ipv6_matches_V6Net(input, view)) by {
            reveal(ipv6_spec::ipv6_matches_V6Net);
        }
        assert(ipv6_spec::ipv6_is_wf_V6Net(input)) by {
            reveal(ipv6_spec::ipv6_is_wf_V6Net);
        }
    }
    assert(ipv6_spec::ipv6_matches_view(input, view)) by {
        reveal(ipv6_spec::ipv6_matches_view);
    }
    ipv6_groups_join_value(left_groups);
    ipv6_groups_join_value(right_groups);
    if compressed {
        if left_groups.len() == 0 {
            reveal(ipv6_spec::triptych_segments_of);
        } else {
            ipv6_groups_join_segments(left_groups);
        }
        if right_groups.len() == 0 {
            reveal(ipv6_spec::triptych_segments_of);
        } else {
            ipv6_groups_join_segments(right_groups);
        }
        ipv6_model_pow_matches(
            8 - left_groups.len() as int,
        );
    } else {
        reveal(ipv6_spec::triptych_segments_of);
    }
    assert(
        ipv6_spec::ipv6_value(
            view.full,
            view.left,
            view.right,
            view.prefix,
        ) == address_value * 129 + prefix_value
    ) by {
        reveal(ipv6_spec::ipv6_value);
        reveal(ipv6_spec::triptych_nat_of);
        if prefix.len() == 0 {
            reveal_with_fuel(
                ipv6_spec::triptych_nat_of_from,
                1,
            );
        }
    }
    assert(ipv6_spec::ipv6_view_denotation(view)
        == address_value * 129 + prefix_value) by {
        reveal(ipv6_spec::ipv6_view_denotation);
    }
    assert(ipv6_spec::ipv6_view_wf_constraints(view)) by {
        reveal(ipv6_spec::ipv6_view_wf_constraints);
        reveal(ipv6_spec::ipv6_wf_constraints);
    }
    ipv6_groups_parse_result_bounds(
        address,
        address_value,
        left_groups,
        right_groups,
        compressed,
    );
    ipv6_generated_address_space();
    assert(
        0 <= address_value * 129 + prefix_value
            <= ipv6_spec::triptych_int_pow(2, 128) * 129 - 1
    );
    assert(ipv6_spec::ipv6_view_constraints(view)) by {
        reveal(ipv6_spec::ipv6_view_constraints);
        reveal(ipv6_spec::ipv6_constraints);
    }
    assert(ipv6_spec::ipv6_view_valid(view)) by {
        reveal(ipv6_spec::ipv6_view_valid);
    }
    assert(crate::ipv6::contract::ipv6_matches_result(
        input,
        address_value * 129 + prefix_value,
    )) by {
        reveal(crate::ipv6::contract::ipv6_matches_result);
        assert(exists|candidate: ipv6_spec::IPv6View|
            ipv6_spec::ipv6_matches_view(input, candidate)
                && ipv6_spec::ipv6_view_valid(candidate)
                && ipv6_spec::ipv6_view_denotation(candidate)
                    == address_value * 129 + prefix_value) by {
            assert(
                ipv6_spec::ipv6_matches_view(input, view)
                    && ipv6_spec::ipv6_view_valid(view)
                    && ipv6_spec::ipv6_view_denotation(view)
                        == address_value * 129 + prefix_value
            );
        }
    }
    assert(ipv6_spec::ipv6_satisfies_wf_constraints(input)) by {
        reveal(ipv6_spec::ipv6_satisfies_wf_constraints);
        assert(exists|candidate: ipv6_spec::IPv6View|
            ipv6_spec::ipv6_matches_view(input, candidate)
                && ipv6_spec::ipv6_view_wf_constraints(candidate)) by {
            assert(
                ipv6_spec::ipv6_matches_view(input, view)
                    && ipv6_spec::ipv6_view_wf_constraints(view)
            );
        }
    }
    assert(ipv6_spec::ipv6_satisfies_constraints(input)) by {
        reveal(ipv6_spec::ipv6_satisfies_constraints);
        assert(exists|candidate: ipv6_spec::IPv6View|
            ipv6_spec::ipv6_matches_view(input, candidate)
                && ipv6_spec::ipv6_view_constraints(candidate)) by {
            assert(
                ipv6_spec::ipv6_matches_view(input, view)
                    && ipv6_spec::ipv6_view_constraints(view)
            );
        }
    }
    assert(ipv6_spec::ipv6_is_wf(input)) by {
        reveal(ipv6_spec::ipv6_is_wf);
    }
    reveal(ipv6_spec::ipv6_is_valid);
}

#[verifier::rlimit(300)]
pub proof fn ipv6_parse_spec_sound(
    input: Seq<char>,
    address_value: int,
    prefix_value: int,
)
    requires
        ipaddr_parse_spec(input) == Some(crate::model::IpAddrSpec {
            family: 6,
            address: address_value,
            prefix: prefix_value,
        }),
    ensures
        crate::ipv6::contract::ipv6_matches_result(
            input,
            address_value * 129 + prefix_value,
        ),
        ipv6_spec::ipv6_is_valid(input),
{
    let slash = ipaddr_find_slash(input, 0);
    reveal(ipaddr_parse_spec);
    assert(is_ascii_chars(input));
    assert(0 < input.len() <= 43);
    ipaddr_find_slash_bounds(input, 0);
    assert(0 < slash <= input.len());
    assert(ipaddr_contains(input, 0, slash, ':'));
    assert(!ipaddr_contains(input, 0, slash, '.'));
    assert(
        crate::model::ipaddr_ipv6_state(
            input,
            0,
            0,
            slash,
            0,
            0,
            0,
            0,
            false,
            0,
            0,
        ) == Some(address_value)
    );
    let empty_characters = Seq::<char>::empty();
    let empty_groups = Seq::<Seq<char>>::empty();
    assert(ipv6_groups_wf(empty_groups)) by {
        reveal(ipv6_groups_wf);
    }
    assert(ipv6_groups_value(empty_groups) == 0) by {
        reveal(ipv6_groups_value);
        reveal(ipv6_groups_value_from);
    }
    assert(
        ipv6_state_text(
            empty_groups,
            empty_groups,
            false,
            empty_characters,
        ) == input.subrange(0, 0)
    ) by {
        reveal(ipv6_state_text);
        assert_seqs_equal!(
            ipv6_state_text(
                empty_groups,
                empty_groups,
                false,
                empty_characters,
            ) == input.subrange(0, 0)
        );
    }
    assert(
        empty_characters == input.subrange(0, 0)
    ) by {
        assert_seqs_equal!(
            empty_characters == input.subrange(0, 0)
        );
    }
    ipv6_state_sound_groups(
        input,
        0,
        0,
        slash,
        0,
        0,
        0,
        0,
        false,
        0,
        0,
        empty_characters,
        empty_groups,
        empty_groups,
        address_value,
    );
    let (left_groups, right_groups, compressed) =
        choose|left_groups: Seq<Seq<char>>,
            right_groups: Seq<Seq<char>>,
            compressed: bool|
            ipv6_groups_parse_result(
                input.subrange(0, slash),
                address_value,
                left_groups,
                right_groups,
                compressed,
            );
    let address = input.subrange(0, slash);
    if slash < input.len() {
        ipaddr_find_slash_found(input, 0);
        assert(input[slash] == '/');
        assert(
            ipaddr_parse_prefix(
                input,
                slash + 1,
                input.len() as int,
                128,
            ) == Some(prefix_value)
        );
        ipaddr_parse_prefix_sound(
            input,
            slash + 1,
            input.len() as int,
            128,
            prefix_value,
        );
        let prefix =
            input.subrange(slash + 1, input.len() as int);
        assert forall|index: int|
            0 <= index < prefix.len() implies
                #[trigger] ipv6_spec::triptych_is_digit(
                    prefix[index],
                ) by {
            assert(
                prefix[index] == input[slash + 1 + index]
            );
            assert(ipv4_spec::triptych_is_digit(
                prefix[index],
            ));
            ipv4_digit_implies_ipv6_digit(prefix[index]);
        }
        ipaddr_decimal_nat_slice(
            input,
            slash + 1,
            input.len() as int,
            prefix,
            0,
            0,
        );
        ipv6_decimal_nat_matches(prefix, 0, 0);
        assert(
            ipv6_spec::triptych_nat_of(prefix)
                == prefix_value
        ) by {
            reveal(ipv6_spec::triptych_nat_of);
            reveal(ipaddr_parse_prefix);
        }
        assert(
            input == address + seq!['/'] + prefix
        ) by {
            assert_seqs_equal!(
                input == address + seq!['/'] + prefix
            );
        }
        assert(
            input == address + (seq!['/'] + prefix)
        ) by {
            assert_seqs_equal!(
                input == address + (seq!['/'] + prefix)
            );
        }
        ipv6_groups_build_valid_view(
            input,
            address,
            prefix,
            address_value,
            prefix_value,
            left_groups,
            right_groups,
            compressed,
        );
    } else {
        assert(slash == input.len());
        assert(prefix_value == 128);
        assert(address == input) by {
            assert_seqs_equal!(address == input);
        }
        ipv6_groups_build_valid_view(
            input,
            address,
            empty_characters,
            address_value,
            prefix_value,
            left_groups,
            right_groups,
            compressed,
        );
    }
}

pub struct IPv4Parts {
    pub oct1: Seq<char>,
    pub oct2: Seq<char>,
    pub oct3: Seq<char>,
    pub oct4: Seq<char>,
}

pub open spec fn ipv4_octet_wf(octet: Seq<char>) -> bool {
    1 <= octet.len()
        && octet.len() <= 3
        && (forall|index: int| 0 <= index < octet.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(octet[index]))
        && (octet[0] != '0' || octet == seq!['0'])
        && 0 <= ipv4_spec::triptych_nat_of(octet)
        && ipv4_spec::triptych_nat_of(octet) <= 255
}

pub open spec fn ipv4_parts_after(
    parts: IPv4Parts,
    completed_segments: int,
) -> bool {
    if completed_segments == 0 {
        ipv4_octet_wf(parts.oct1)
            && ipv4_octet_wf(parts.oct2)
            && ipv4_octet_wf(parts.oct3)
            && ipv4_octet_wf(parts.oct4)
    } else if completed_segments == 1 {
        parts.oct1.len() == 0
            && ipv4_octet_wf(parts.oct2)
            && ipv4_octet_wf(parts.oct3)
            && ipv4_octet_wf(parts.oct4)
    } else if completed_segments == 2 {
        parts.oct1.len() == 0
            && parts.oct2.len() == 0
            && ipv4_octet_wf(parts.oct3)
            && ipv4_octet_wf(parts.oct4)
    } else if completed_segments == 3 {
        parts.oct1.len() == 0
            && parts.oct2.len() == 0
            && parts.oct3.len() == 0
            && ipv4_octet_wf(parts.oct4)
    } else {
        false
    }
}

pub open spec fn ipv4_parts_text_after(
    parts: IPv4Parts,
    completed_segments: int,
) -> Seq<char> {
    if completed_segments == 0 {
        parts.oct1 + seq!['.'] + parts.oct2 + seq!['.']
            + parts.oct3 + seq!['.'] + parts.oct4
    } else if completed_segments == 1 {
        parts.oct2 + seq!['.'] + parts.oct3 + seq!['.'] + parts.oct4
    } else if completed_segments == 2 {
        parts.oct3 + seq!['.'] + parts.oct4
    } else {
        parts.oct4
    }
}

pub open spec fn ipv4_parts_value_after(
    parts: IPv4Parts,
    completed_segments: int,
    address: int,
) -> int {
    if completed_segments == 0 {
        (((address * 256 + ipv4_spec::triptych_nat_of(parts.oct1))
            * 256 + ipv4_spec::triptych_nat_of(parts.oct2))
            * 256 + ipv4_spec::triptych_nat_of(parts.oct3))
            * 256 + ipv4_spec::triptych_nat_of(parts.oct4)
    } else if completed_segments == 1 {
        ((address * 256 + ipv4_spec::triptych_nat_of(parts.oct2))
            * 256 + ipv4_spec::triptych_nat_of(parts.oct3))
            * 256 + ipv4_spec::triptych_nat_of(parts.oct4)
    } else if completed_segments == 2 {
        (address * 256 + ipv4_spec::triptych_nat_of(parts.oct3))
            * 256 + ipv4_spec::triptych_nat_of(parts.oct4)
    } else {
        address * 256 + ipv4_spec::triptych_nat_of(parts.oct4)
    }
}

pub proof fn ipv4_triptych_nat_of_from_push_digit(
    characters: Seq<char>,
    index: int,
    accumulator: int,
    digit: char,
)
    requires
        0 <= index <= characters.len(),
        ipv4_spec::triptych_is_digit(digit),
    ensures
        ipv4_spec::triptych_nat_of_from(
            characters.push(digit),
            index,
            accumulator,
        ) == ipv4_spec::triptych_nat_of_from(
            characters,
            index,
            accumulator,
        ) * 10
                + (digit as int - ipv4_spec::TRIPTYCH_ZERO as int),
    decreases characters.len() - index,
{
    if index < characters.len() {
        ipv4_triptych_nat_of_from_push_digit(
            characters,
            index + 1,
            accumulator * 10
                + if (characters[index] as int)
                    < (ipv4_spec::TRIPTYCH_ZERO as int) {
                    0
                } else {
                    (characters[index] as int)
                        - (ipv4_spec::TRIPTYCH_ZERO as int)
                },
            digit,
        );
        reveal(ipv4_spec::triptych_nat_of_from);
    } else {
        assert(characters.push(digit)[index] == digit);
        reveal(ipv4_spec::triptych_is_digit);
        reveal_with_fuel(ipv4_spec::triptych_nat_of_from, 2);
    }
}

pub proof fn ipv4_triptych_nat_of_push_digit(
    characters: Seq<char>,
    digit: char,
)
    requires
        ipv4_spec::triptych_is_digit(digit),
    ensures
        ipv4_spec::triptych_nat_of(characters.push(digit))
            == ipv4_spec::triptych_nat_of(characters) * 10
                + (digit as int - ipv4_spec::TRIPTYCH_ZERO as int),
{
    ipv4_triptych_nat_of_from_push_digit(characters, 0, 0, digit);
    reveal(ipv4_spec::triptych_nat_of);
}

pub proof fn ipv4_scale_256_bounds(value: int, maximum: int)
    requires
        0 <= value <= maximum,
        0 <= maximum,
    ensures
        0 <= value * 256 <= maximum * 256,
{
    lemma_mul_left_inequality(256, 0, value);
    lemma_mul_left_inequality(256, value, maximum);
    lemma_mul_is_commutative(256, value);
    lemma_mul_is_commutative(256, maximum);
}

#[verifier::rlimit(150)]
pub proof fn ipv4_state_sound_parts(
    input: Seq<char>,
    component_start: int,
    index: int,
    end: int,
    completed_segments: int,
    address: int,
    octet: int,
    digits: int,
    result: int,
)
    requires
        0 <= component_start <= index <= end <= input.len(),
        0 <= completed_segments <= 3,
        0 <= address,
        0 <= octet <= 255,
        0 <= digits <= 3,
        digits == index - component_start,
        octet == ipv4_spec::triptych_nat_of(
            input.subrange(component_start, index),
        ),
        forall|position: int| component_start <= position < index ==>
            #[trigger] ipv4_spec::triptych_is_digit(input[position]),
        component_start == index
            || input[component_start] != '0'
            || input.subrange(component_start, index) == seq!['0'],
        ipaddr_ipv4_state(
            input,
            index,
            end,
            completed_segments,
            address,
            octet,
            digits,
        ) == Some(result),
    ensures
        exists|parts: IPv4Parts|
            input.subrange(component_start, end)
                == ipv4_parts_text_after(parts, completed_segments)
                && ipv4_parts_after(parts, completed_segments)
                && result == ipv4_parts_value_after(
                    parts,
                    completed_segments,
                    address,
                ),
    decreases end - index,
{
    let current = input.subrange(component_start, index);
    reveal(ipaddr_ipv4_state);
    if index == end {
        assert(completed_segments == 3);
        assert(0 < digits);
        let empty = Seq::<char>::empty();
        let parts = IPv4Parts {
            oct1: empty,
            oct2: empty,
            oct3: empty,
            oct4: current,
        };
        assert(input.subrange(component_start, end) == current);
        assert(ipv4_octet_wf(current)) by {
            reveal(ipv4_octet_wf);
            assert forall|position: int| 0 <= position < current.len() implies
                #[trigger] ipv4_spec::triptych_is_digit(
                    current[position],
                ) by {
                assert(
                    current[position]
                        == input[component_start + position]
                );
            }
            if current[0] == '0' {
                assert(input[component_start] == '0');
            }
        }
        assert(ipv4_parts_after(parts, completed_segments)) by {
            reveal(ipv4_parts_after);
        }
        assert(
            ipv4_parts_text_after(parts, completed_segments) == current
        ) by {
            reveal(ipv4_parts_text_after);
        }
        assert(
            ipv4_parts_value_after(
                parts,
                completed_segments,
                address,
            ) == address * 256 + octet
        ) by {
            reveal(ipv4_parts_value_after);
        }
        assert(exists|candidate: IPv4Parts|
            input.subrange(component_start, end)
                    == ipv4_parts_text_after(
                        candidate,
                        completed_segments,
                    )
                && ipv4_parts_after(candidate, completed_segments)
                && result == ipv4_parts_value_after(
                    candidate,
                    completed_segments,
                    address,
                )) by {
            assert(
                input.subrange(component_start, end)
                        == ipv4_parts_text_after(
                            parts,
                            completed_segments,
                        )
                    && ipv4_parts_after(parts, completed_segments)
                    && result == ipv4_parts_value_after(
                        parts,
                        completed_segments,
                        address,
                    )
            );
        }
    } else if ipaddr_is_digit(input[index]) {
        let next_octet =
            octet * 10 + ipaddr_digit_value(input[index]);
        let next_current =
            input.subrange(component_start, index + 1);
        if digits == 3
            || (0 < digits && octet == 0)
            || next_octet > 255
        {
            assert(false);
        } else {
            assert(ipv4_spec::triptych_is_digit(input[index])) by {
                reveal(ipaddr_is_digit);
                reveal(ipv4_spec::triptych_is_digit);
            }
            assert(
                ipaddr_digit_value(input[index])
                    == input[index] as int
                        - ipv4_spec::TRIPTYCH_ZERO as int
            ) by {
                reveal(ipaddr_digit_value);
            }
            assert(next_current == current.push(input[index])) by {
                assert_seqs_equal!(
                    next_current == current.push(input[index])
                );
            }
            ipv4_triptych_nat_of_push_digit(
                current,
                input[index],
            );
            assert(
                next_octet
                    == ipv4_spec::triptych_nat_of(next_current)
            );
            assert forall|position: int|
                component_start <= position < index + 1 implies
                #[trigger] ipv4_spec::triptych_is_digit(
                    input[position],
                ) by {
                if position < index {
                } else {
                    assert(position == index);
                }
            }
            assert(
                component_start == index + 1
                    || input[component_start] != '0'
                    || next_current == seq!['0']
            ) by {
                if input[component_start] == '0' {
                    if component_start < index {
                        assert(current[0] == '0');
                        assert(current == seq!['0']);
                        assert(current.len() == 1);
                        reveal(ipv4_spec::triptych_nat_of);
                        reveal_with_fuel(
                            ipv4_spec::triptych_nat_of_from,
                            2,
                        );
                        assert(octet == 0);
                        assert(false);
                    } else {
                        assert(next_current.len() == 1);
                        assert(next_current[0] == '0');
                        assert_seqs_equal!(
                            next_current == seq!['0']
                        );
                    }
                }
            }
            assert(0 <= ipaddr_digit_value(input[index])) by {
                reveal(ipaddr_is_digit);
                reveal(ipaddr_digit_value);
            }
            ipv4_state_sound_parts(
                input,
                component_start,
                index + 1,
                end,
                completed_segments,
                address,
                next_octet,
                digits + 1,
                result,
            );
        }
    } else if input[index] == '.'
        && 0 < digits
        && completed_segments < 3
    {
        let next = index + 1;
        ipv4_state_sound_parts(
            input,
            next,
            next,
            end,
            completed_segments + 1,
            address * 256 + octet,
            0,
            0,
            result,
        );
        let tail = choose|parts: IPv4Parts|
            input.subrange(next, end)
                    == ipv4_parts_text_after(
                        parts,
                        completed_segments + 1,
                    )
                && #[trigger] ipv4_parts_after(
                    parts,
                    completed_segments + 1,
                )
                && result == ipv4_parts_value_after(
                    parts,
                    completed_segments + 1,
                    address * 256 + octet,
                );
        assert(ipv4_octet_wf(current)) by {
            reveal(ipv4_octet_wf);
            assert forall|position: int| 0 <= position < current.len() implies
                #[trigger] ipv4_spec::triptych_is_digit(
                    current[position],
                ) by {
                assert(
                    current[position]
                        == input[component_start + position]
                );
            }
            if current[0] == '0' {
                assert(input[component_start] == '0');
            }
        }
        let parts = if completed_segments == 0 {
            IPv4Parts {
                oct1: current,
                oct2: tail.oct2,
                oct3: tail.oct3,
                oct4: tail.oct4,
            }
        } else if completed_segments == 1 {
            IPv4Parts {
                oct1: tail.oct1,
                oct2: current,
                oct3: tail.oct3,
                oct4: tail.oct4,
            }
        } else {
            IPv4Parts {
                oct1: tail.oct1,
                oct2: tail.oct2,
                oct3: current,
                oct4: tail.oct4,
            }
        };
        assert(
            input.subrange(component_start, end)
                == current + seq!['.'] + input.subrange(next, end)
        ) by {
            assert(input[index] == '.');
            assert_seqs_equal!(
                input.subrange(component_start, end)
                    == current
                        + seq!['.']
                        + input.subrange(next, end)
            );
        }
        assert(ipv4_parts_after(parts, completed_segments)) by {
            reveal(ipv4_parts_after);
        }
        assert(
            ipv4_parts_text_after(parts, completed_segments)
                == current
                    + seq!['.']
                    + ipv4_parts_text_after(
                        tail,
                        completed_segments + 1,
                    )
        ) by {
            reveal(ipv4_parts_text_after);
        }
        assert(
            ipv4_parts_value_after(
                parts,
                completed_segments,
                address,
            ) == ipv4_parts_value_after(
                tail,
                completed_segments + 1,
                address * 256 + octet,
            )
        ) by {
            reveal(ipv4_parts_value_after);
        }
        assert(exists|candidate: IPv4Parts|
            input.subrange(component_start, end)
                    == ipv4_parts_text_after(
                        candidate,
                        completed_segments,
                    )
                && ipv4_parts_after(candidate, completed_segments)
                && result == ipv4_parts_value_after(
                    candidate,
                    completed_segments,
                    address,
                )) by {
            assert(
                input.subrange(component_start, end)
                        == ipv4_parts_text_after(
                            parts,
                            completed_segments,
                        )
                    && ipv4_parts_after(parts, completed_segments)
                    && result == ipv4_parts_value_after(
                        parts,
                        completed_segments,
                        address,
                    )
            );
        }
    } else {
        assert(false);
    }
}

pub proof fn ipv4_matches_address_implies_wf(
    input: Seq<char>,
    view: ipv4_spec::IPv4View,
)
    requires
        ipv4_spec::ipv4_matches_V4Addr(input, view),
    ensures
        ipv4_spec::ipv4_is_wf_V4Addr(input),
{
    reveal(ipv4_spec::ipv4_matches_V4Addr);
    let (oct1, oct2, oct3, oct4) =
        choose|oct1: Seq<char>, oct2: Seq<char>, oct3: Seq<char>,
            oct4: Seq<char>|
            input == oct1 + seq!['.'] + oct2 + seq!['.'] + oct3
                + seq!['.'] + oct4
                && (view.oct1 == oct1
                    && #[trigger] ipv4_spec::ipv4_matches_Oct1(oct1, view))
                && (view.oct2 == oct2
                    && #[trigger] ipv4_spec::ipv4_matches_Oct2(oct2, view))
                && (view.oct3 == oct3
                    && #[trigger] ipv4_spec::ipv4_matches_Oct3(oct3, view))
                && (view.oct4 == oct4
                    && #[trigger] ipv4_spec::ipv4_matches_Oct4(oct4, view));
    assert(ipv4_spec::ipv4_is_wf_Oct1(oct1)) by {
        reveal(ipv4_spec::ipv4_matches_Oct1);
        reveal(ipv4_spec::ipv4_is_wf_Oct1);
    }
    assert(ipv4_spec::ipv4_is_wf_Oct2(oct2)) by {
        reveal(ipv4_spec::ipv4_matches_Oct2);
        reveal(ipv4_spec::ipv4_is_wf_Oct2);
    }
    assert(ipv4_spec::ipv4_is_wf_Oct3(oct3)) by {
        reveal(ipv4_spec::ipv4_matches_Oct3);
        reveal(ipv4_spec::ipv4_is_wf_Oct3);
    }
    assert(ipv4_spec::ipv4_is_wf_Oct4(oct4)) by {
        reveal(ipv4_spec::ipv4_matches_Oct4);
        reveal(ipv4_spec::ipv4_is_wf_Oct4);
    }
    reveal(ipv4_spec::ipv4_is_wf_V4Addr);
}

pub proof fn ipv4_matches_prefix_implies_wf(
    input: Seq<char>,
    view: ipv4_spec::IPv4View,
)
    requires
        ipv4_spec::ipv4_matches_Prefix(input, view),
    ensures
        ipv4_spec::ipv4_is_wf_Prefix(input),
{
    reveal(ipv4_spec::ipv4_matches_Prefix);
    reveal(ipv4_spec::ipv4_is_wf_Prefix);
}

#[verifier::spinoff_prover]
pub proof fn ipv4_matches_net_implies_wf(
    input: Seq<char>,
    view: ipv4_spec::IPv4View,
)
    requires
        ipv4_spec::ipv4_matches_V4Net(input, view),
    ensures
        ipv4_spec::ipv4_is_wf_V4Net(input),
{
    reveal(ipv4_spec::ipv4_matches_V4Net);
    if exists|v4_addr: Seq<char>|
        input == v4_addr
            && ipv4_spec::ipv4_matches_V4Addr(v4_addr, view)
            && view.prefix == seq![]
    {
        let v4_addr = choose|v4_addr: Seq<char>|
            input == v4_addr
                && #[trigger] ipv4_spec::ipv4_matches_V4Addr(
                    v4_addr,
                    view,
                )
                && view.prefix == seq![];
        ipv4_matches_address_implies_wf(v4_addr, view);
        reveal(ipv4_spec::ipv4_is_wf_V4Net);
    } else {
        let (v4_addr, prefix) =
            choose|v4_addr: Seq<char>, prefix: Seq<char>|
                input == v4_addr + seq!['/'] + prefix
                    && #[trigger] ipv4_spec::ipv4_matches_V4Addr(
                        v4_addr,
                        view,
                    )
                    && view.prefix == prefix
                    && #[trigger] ipv4_spec::ipv4_matches_Prefix(
                        prefix,
                        view,
                    );
        ipv4_matches_address_implies_wf(v4_addr, view);
        ipv4_matches_prefix_implies_wf(prefix, view);
        reveal(ipv4_spec::ipv4_is_wf_V4Net);
    }
}

#[verifier::spinoff_prover]
pub proof fn ipv4_view_implies_valid(
    input: Seq<char>,
    view: ipv4_spec::IPv4View,
)
    requires
        ipv4_spec::ipv4_matches_view(input, view),
        ipv4_spec::ipv4_view_valid(view),
    ensures
        ipv4_spec::ipv4_is_valid(input),
{
    reveal(ipv4_spec::ipv4_matches_view);
    ipv4_matches_net_implies_wf(input, view);
    reveal(ipv4_spec::ipv4_view_valid);
    assert(ipv4_spec::ipv4_view_wf_constraints(view));
    assert(ipv4_spec::ipv4_view_constraints(view));
    assert(ipv4_spec::ipv4_satisfies_wf_constraints(input)) by {
        reveal(ipv4_spec::ipv4_satisfies_wf_constraints);
        assert(exists|candidate: ipv4_spec::IPv4View|
            ipv4_spec::ipv4_matches_view(input, candidate)
                && ipv4_spec::ipv4_view_wf_constraints(candidate)) by {
            assert(
                ipv4_spec::ipv4_matches_view(input, view)
                    && ipv4_spec::ipv4_view_wf_constraints(view)
            );
        }
    }
    assert(ipv4_spec::ipv4_satisfies_constraints(input)) by {
        reveal(ipv4_spec::ipv4_satisfies_constraints);
        assert(exists|candidate: ipv4_spec::IPv4View|
            ipv4_spec::ipv4_matches_view(input, candidate)
                && ipv4_spec::ipv4_view_constraints(candidate)) by {
            assert(
                ipv4_spec::ipv4_matches_view(input, view)
                    && ipv4_spec::ipv4_view_constraints(view)
            );
        }
    }
    reveal(ipv4_spec::ipv4_is_valid);
    reveal(ipv4_spec::ipv4_is_wf);
}

#[verifier::rlimit(100)]
pub proof fn ipv4_parts_build_valid_view(
    input: Seq<char>,
    parts: IPv4Parts,
    prefix: Seq<char>,
    address: int,
    prefix_value: int,
)
    requires
        input == ipv4_parts_text_after(parts, 0)
            + if prefix.len() == 0 {
                Seq::<char>::empty()
            } else {
                seq!['/'] + prefix
            },
        ipv4_parts_after(parts, 0),
        address == ipv4_parts_value_after(parts, 0, 0),
        prefix.len() == 0 || (
            1 <= prefix.len() <= 2
                && (forall|index: int| 0 <= index < prefix.len() ==>
                    #[trigger] ipv4_spec::triptych_is_digit(prefix[index]))
                && (prefix[0] != '0' || prefix == seq!['0'])
                && 0 <= ipv4_spec::triptych_nat_of(prefix) <= 32
        ),
        prefix_value == if prefix.len() == 0 {
            32
        } else {
            ipv4_spec::triptych_nat_of(prefix)
        },
    ensures
        crate::ipv4::contract::ipv4_matches_result(
            input,
            address * 33 + prefix_value,
        ),
        ipv4_spec::ipv4_is_valid(input),
{
    let address_text = ipv4_parts_text_after(parts, 0);
    let view = ipv4_spec::IPv4View {
        input,
        oct1: parts.oct1,
        oct2: parts.oct2,
        oct3: parts.oct3,
        oct4: parts.oct4,
        prefix,
    };
    reveal(ipv4_parts_after);
    reveal(ipv4_octet_wf);
    assert(ipv4_spec::ipv4_matches_Oct1(parts.oct1, view)) by {
        reveal(ipv4_spec::ipv4_matches_Oct1);
    }
    assert(ipv4_spec::ipv4_matches_Oct2(parts.oct2, view)) by {
        reveal(ipv4_spec::ipv4_matches_Oct2);
    }
    assert(ipv4_spec::ipv4_matches_Oct3(parts.oct3, view)) by {
        reveal(ipv4_spec::ipv4_matches_Oct3);
    }
    assert(ipv4_spec::ipv4_matches_Oct4(parts.oct4, view)) by {
        reveal(ipv4_spec::ipv4_matches_Oct4);
    }
    assert(ipv4_spec::ipv4_matches_V4Addr(address_text, view)) by {
        reveal(ipv4_parts_text_after);
        reveal(ipv4_spec::ipv4_matches_V4Addr);
    }
    if prefix.len() == 0 {
        assert(prefix == seq![]) by {
            assert_seqs_equal!(prefix == seq![]);
        }
        assert(ipv4_spec::ipv4_matches_V4Net(input, view)) by {
            reveal(ipv4_spec::ipv4_matches_V4Net);
        }
    } else {
        assert(input == address_text + seq!['/'] + prefix);
        assert(ipv4_spec::ipv4_matches_Prefix(prefix, view)) by {
            reveal(ipv4_spec::ipv4_matches_Prefix);
        }
        assert(ipv4_spec::ipv4_matches_V4Net(input, view)) by {
            reveal(ipv4_spec::ipv4_matches_V4Net);
        }
    }
    assert(ipv4_spec::ipv4_matches_view(input, view)) by {
        reveal(ipv4_spec::ipv4_matches_view);
    }
    assert(ipv4_spec::ipv4_view_wf_constraints(view)) by {
        reveal(ipv4_spec::ipv4_view_wf_constraints);
        reveal(ipv4_spec::ipv4_wf_constraints);
    }
    assert(
        address
            == (((ipv4_spec::triptych_nat_of(parts.oct1) * 256
                + ipv4_spec::triptych_nat_of(parts.oct2)) * 256
                + ipv4_spec::triptych_nat_of(parts.oct3)) * 256
                + ipv4_spec::triptych_nat_of(parts.oct4))
    ) by {
        reveal(ipv4_parts_value_after);
    }
    let octet1 = ipv4_spec::triptych_nat_of(parts.oct1);
    let octet2 = ipv4_spec::triptych_nat_of(parts.oct2);
    let octet3 = ipv4_spec::triptych_nat_of(parts.oct3);
    let octet4 = ipv4_spec::triptych_nat_of(parts.oct4);
    assert(0 <= octet1 <= 255);
    assert(0 <= octet2 <= 255);
    assert(0 <= octet3 <= 255);
    assert(0 <= octet4 <= 255);
    let first_two = octet1 * 256 + octet2;
    let first_three = first_two * 256 + octet3;
    let all_four = first_three * 256 + octet4;
    ipv4_scale_256_bounds(octet1, 255);
    assert(0 <= first_two <= 65_535);
    ipv4_scale_256_bounds(first_two, 65_535);
    assert(0 <= first_three <= 16_777_215);
    ipv4_scale_256_bounds(first_three, 16_777_215);
    assert(0 <= all_four <= 4_294_967_295);
    assert(address == all_four);
    assert(
        ipv4_spec::ipv4_view_denotation(view)
            == address * 33 + prefix_value
    ) by {
        reveal(ipv4_spec::ipv4_view_denotation);
        reveal(ipv4_spec::ipv4_value);
    }
    assert(ipv4_spec::triptych_int_pow(2, 32) == 4_294_967_296) by {
        reveal_with_fuel(ipv4_spec::triptych_int_pow, 33);
    }
    assert(ipv4_spec::ipv4_view_constraints(view)) by {
        reveal(ipv4_spec::ipv4_view_constraints);
        reveal(ipv4_spec::ipv4_constraints);
    }
    assert(ipv4_spec::ipv4_view_valid(view)) by {
        reveal(ipv4_spec::ipv4_view_valid);
    }
    assert(crate::ipv4::contract::ipv4_matches_result(
        input,
        address * 33 + prefix_value,
    )) by {
        reveal(crate::ipv4::contract::ipv4_matches_result);
        assert(exists|candidate: ipv4_spec::IPv4View|
            ipv4_spec::ipv4_matches_view(input, candidate)
                && ipv4_spec::ipv4_view_valid(candidate)
                && ipv4_spec::ipv4_view_denotation(candidate)
                    == address * 33 + prefix_value) by {
            assert(
                ipv4_spec::ipv4_matches_view(input, view)
                    && ipv4_spec::ipv4_view_valid(view)
                    && ipv4_spec::ipv4_view_denotation(view)
                        == address * 33 + prefix_value
            );
        }
    }
    ipv4_view_implies_valid(input, view);
}

#[verifier::rlimit(150)]
pub proof fn ipv4_parse_spec_sound(
    input: Seq<char>,
    address: int,
    prefix_value: int,
)
    requires
        ipaddr_parse_spec(input) == Some(crate::model::IpAddrSpec {
            family: 4,
            address,
            prefix: prefix_value,
        }),
    ensures
        crate::ipv4::contract::ipv4_matches_result(
            input,
            address * 33 + prefix_value,
        ),
        ipv4_spec::ipv4_is_valid(input),
{
    let slash = ipaddr_find_slash(input, 0);
    reveal(ipaddr_parse_spec);
    assert(is_ascii_chars(input));
    assert(0 < input.len() <= 43);
    ipaddr_find_slash_bounds(input, 0);
    assert(0 < slash <= input.len());
    assert(ipaddr_contains(input, 0, slash, '.'));
    assert(!ipaddr_contains(input, 0, slash, ':'));
    assert(
        ipaddr_ipv4_state(input, 0, slash, 0, 0, 0, 0)
            == Some(address)
    );
    let empty = Seq::<char>::empty();
    assert(ipv4_spec::triptych_nat_of(empty) == 0) by {
        reveal(ipv4_spec::triptych_nat_of);
        reveal_with_fuel(ipv4_spec::triptych_nat_of_from, 2);
    }
    ipv4_state_sound_parts(
        input,
        0,
        0,
        slash,
        0,
        0,
        0,
        0,
        address,
    );
    let parts = choose|parts: IPv4Parts|
        input.subrange(0, slash)
                == ipv4_parts_text_after(parts, 0)
            && #[trigger] ipv4_parts_after(parts, 0)
            && address == ipv4_parts_value_after(parts, 0, 0);
    if slash < input.len() {
        ipaddr_find_slash_found(input, 0);
        assert(
            ipaddr_parse_prefix(
                input,
                slash + 1,
                input.len() as int,
                32,
            ) == Some(prefix_value)
        );
        ipaddr_parse_prefix_sound(
            input,
            slash + 1,
            input.len() as int,
            32,
            prefix_value,
        );
        let prefix =
            input.subrange(slash + 1, input.len() as int);
        assert(input[slash] == '/');
        assert(0 < prefix.len());
        assert(
            input
                == input.subrange(0, slash)
                    + seq!['/']
                    + prefix
        ) by {
            assert_seqs_equal!(
                input
                    == input.subrange(0, slash)
                        + seq!['/']
                        + prefix
            );
        }
        assert(
            input
                == ipv4_parts_text_after(parts, 0)
                    + seq!['/']
                    + prefix
        );
        assert(
            input == ipv4_parts_text_after(parts, 0)
                + if prefix.len() == 0 {
                    Seq::<char>::empty()
                } else {
                    seq!['/'] + prefix
                }
        );
        ipv4_parts_build_valid_view(
            input,
            parts,
            prefix,
            address,
            prefix_value,
        );
    } else {
        assert(slash == input.len());
        assert(prefix_value == 32);
        assert(input.subrange(0, slash) == input) by {
            assert_seqs_equal!(input.subrange(0, slash) == input);
        }
        assert(input == ipv4_parts_text_after(parts, 0));
        ipv4_parts_build_valid_view(
            input,
            parts,
            empty,
            address,
            prefix_value,
        );
    }
}

#[verifier::rlimit(100)]
pub proof fn ipv4_wf_match_has_result(
    input: Seq<char>,
    view: ipv4_spec::IPv4View,
)
    requires
        ipv4_spec::ipv4_matches_view(input, view),
        ipv4_spec::ipv4_view_wf_constraints(view),
    ensures
        exists|value: int|
            crate::ipv4::contract::ipv4_matches_result(input, value),
{
    reveal(ipv4_spec::ipv4_matches_view);
    reveal(ipv4_spec::ipv4_matches_V4Net);
    reveal(ipv4_spec::ipv4_matches_V4Addr);
    reveal(ipv4_spec::ipv4_matches_Oct1);
    reveal(ipv4_spec::ipv4_matches_Oct2);
    reveal(ipv4_spec::ipv4_matches_Oct3);
    reveal(ipv4_spec::ipv4_matches_Oct4);
    reveal(ipv4_spec::ipv4_matches_Prefix);
    reveal(ipv4_spec::ipv4_view_wf_constraints);
    reveal(ipv4_spec::ipv4_wf_constraints);
    let parts = IPv4Parts {
        oct1: view.oct1,
        oct2: view.oct2,
        oct3: view.oct3,
        oct4: view.oct4,
    };
    let prefix = view.prefix;
    let address = ipv4_parts_value_after(parts, 0, 0);
    let prefix_value = if prefix.len() == 0 {
        32
    } else {
        ipv4_spec::triptych_nat_of(prefix)
    };
    assert(ipv4_parts_after(parts, 0)) by {
        reveal(ipv4_parts_after);
        reveal(ipv4_octet_wf);
    }
    assert(
        input == ipv4_parts_text_after(parts, 0)
            + if prefix.len() == 0 {
                Seq::<char>::empty()
            } else {
                seq!['/'] + prefix
            }
    ) by {
        reveal(ipv4_parts_text_after);
    }
    assert(
        prefix.len() == 0 || (
            1 <= prefix.len() <= 2
                && (forall|index: int| 0 <= index < prefix.len() ==>
                    #[trigger] ipv4_spec::triptych_is_digit(prefix[index]))
                && (prefix[0] != '0' || prefix == seq!['0'])
                && 0 <= ipv4_spec::triptych_nat_of(prefix) <= 32
        )
    );
    ipv4_parts_build_valid_view(
        input,
        parts,
        prefix,
        address,
        prefix_value,
    );
    assert(exists|value: int|
        crate::ipv4::contract::ipv4_matches_result(input, value)) by {
        assert(crate::ipv4::contract::ipv4_matches_result(
            input,
            address * 33 + prefix_value,
        ));
    }
}

pub proof fn ipv4_valid_has_result(input: Seq<char>)
    requires
        ipv4_spec::ipv4_is_valid(input),
    ensures
        exists|value: int|
            crate::ipv4::contract::ipv4_matches_result(input, value),
{
    reveal(ipv4_spec::ipv4_is_valid);
    reveal(ipv4_spec::ipv4_is_wf);
    reveal(ipv4_spec::ipv4_satisfies_wf_constraints);
    let view = choose|view: ipv4_spec::IPv4View|
        ipv4_spec::ipv4_matches_view(input, view)
            && #[trigger] ipv4_spec::ipv4_view_wf_constraints(view);
    ipv4_wf_match_has_result(input, view);
}

pub proof fn ipaddr_ascii_concat(left: Seq<char>, right: Seq<char>)
    requires
        is_ascii_chars(left),
        is_ascii_chars(right),
    ensures
        is_ascii_chars(left + right),
{
    reveal(is_ascii_chars);
    assert forall|index: int| 0 <= index < (left + right).len() implies
        '\0' <= #[trigger] (left + right)[index] <= '\u{7f}' by {
        if index < left.len() {
            assert((left + right)[index] == left[index]);
        } else {
            assert((left + right)[index] == right[index - left.len()]);
        }
    }
}

pub proof fn ipv4_digit_sequence_ascii(characters: Seq<char>)
    requires
        forall|index: int| 0 <= index < characters.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(characters[index]),
    ensures
        is_ascii_chars(characters),
{
    reveal(is_ascii_chars);
    assert forall|index: int| 0 <= index < characters.len() implies
        '\0' <= #[trigger] characters[index] <= '\u{7f}' by {
        assert(ipv4_spec::triptych_is_digit(characters[index]));
        reveal(ipv4_spec::triptych_is_digit);
    }
}

pub proof fn ipv4_decimal_nat_matches(
    characters: Seq<char>,
    index: int,
    accumulator: int,
)
    requires
        0 <= index <= characters.len(),
        0 <= accumulator,
        forall|checked: int| index <= checked < characters.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(characters[checked]),
    ensures
        ipaddr_decimal_nat(
            characters,
            index,
            characters.len() as int,
            accumulator,
        ) == Some(
            ipv4_spec::triptych_nat_of_from(
                characters,
                index,
                accumulator,
            ),
        ),
    decreases characters.len() - index,
{
    if index < characters.len() {
        assert(ipv4_spec::triptych_is_digit(characters[index]));
        assert(ipaddr_is_digit(characters[index])) by {
            reveal(ipaddr_is_digit);
            reveal(ipv4_spec::triptych_is_digit);
        }
        assert(
            ipaddr_digit_value(characters[index])
                == if (characters[index] as int)
                    < (ipv4_spec::TRIPTYCH_ZERO as int) {
                    0
                } else {
                    (characters[index] as int)
                        - (ipv4_spec::TRIPTYCH_ZERO as int)
                }
        ) by {
            reveal(ipaddr_digit_value);
            reveal(ipaddr_is_digit);
        }
        assert forall|checked: int|
            index + 1 <= checked < characters.len() implies
                #[trigger] ipv4_spec::triptych_is_digit(
                    characters[checked],
                ) by {}
        ipv4_decimal_nat_matches(
            characters,
            index + 1,
            accumulator * 10 + ipaddr_digit_value(characters[index]),
        );
        reveal(ipaddr_decimal_nat);
        reveal(ipv4_spec::triptych_nat_of_from);
    } else {
        reveal(ipaddr_decimal_nat);
        reveal(ipv4_spec::triptych_nat_of_from);
    }
}

pub proof fn ipaddr_find_slash_absent(input: Seq<char>, index: int)
    requires
        0 <= index <= input.len(),
        forall|checked: int| index <= checked < input.len() ==>
            #[trigger] input[checked] != '/',
    ensures
        ipaddr_find_slash(input, index) == input.len(),
    decreases input.len() - index,
{
    if index < input.len() {
        assert(input[index] != '/');
        ipaddr_find_slash_absent(input, index + 1);
    }
    reveal(ipaddr_find_slash);
}

pub proof fn ipaddr_find_slash_bounds(input: Seq<char>, index: int)
    requires
        0 <= index <= input.len(),
    ensures
        index <= ipaddr_find_slash(input, index) <= input.len(),
    decreases input.len() - index,
{
    if index < input.len() && input[index] != '/' {
        ipaddr_find_slash_bounds(input, index + 1);
    }
    reveal(ipaddr_find_slash);
}

pub proof fn ipaddr_find_slash_found(input: Seq<char>, index: int)
    requires
        0 <= index <= input.len(),
        ipaddr_find_slash(input, index) < input.len(),
    ensures
        input[ipaddr_find_slash(input, index)] == '/',
    decreases input.len() - index,
{
    if index < input.len() && input[index] != '/' {
        ipaddr_find_slash_found(input, index + 1);
    }
    reveal(ipaddr_find_slash);
}

pub proof fn ipaddr_find_slash_after_prefix(
    input: Seq<char>,
    prefix_end: int,
    index: int,
)
    requires
        0 <= index <= prefix_end < input.len(),
        input[prefix_end] == '/',
        forall|checked: int| index <= checked < prefix_end ==>
            #[trigger] input[checked] != '/',
    ensures
        ipaddr_find_slash(input, index) == prefix_end,
    decreases prefix_end - index,
{
    if index < prefix_end {
        assert(input[index] != '/');
        ipaddr_find_slash_after_prefix(input, prefix_end, index + 1);
    }
    reveal(ipaddr_find_slash);
}

pub proof fn ipaddr_contains_prefix_extensional(
    input: Seq<char>,
    prefix: Seq<char>,
    start: int,
    end: int,
    character: char,
)
    requires
        0 <= start <= end <= input.len(),
        end == prefix.len(),
        input.subrange(0, end) == prefix,
    ensures
        ipaddr_contains(input, start, end, character)
            == ipaddr_contains(prefix, start, end, character),
    decreases end - start,
{
    if start < end {
        assert(input[start] == prefix[start]);
        ipaddr_contains_prefix_extensional(
            input,
            prefix,
            start + 1,
            end,
            character,
        );
    }
    reveal(ipaddr_contains);
}

pub proof fn ipaddr_contains_absent(
    input: Seq<char>,
    start: int,
    end: int,
    character: char,
)
    requires
        0 <= start <= end <= input.len(),
        forall|checked: int| start <= checked < end ==>
            #[trigger] input[checked] != character,
    ensures
        !ipaddr_contains(input, start, end, character),
    decreases end - start,
{
    if start < end {
        assert(input[start] != character);
        ipaddr_contains_absent(input, start + 1, end, character);
    }
    reveal(ipaddr_contains);
}

pub proof fn ipaddr_decimal_nat_slice(
    input: Seq<char>,
    start: int,
    end: int,
    characters: Seq<char>,
    index: int,
    accumulator: int,
)
    requires
        0 <= start <= end <= input.len(),
        input.subrange(start, end) == characters,
        0 <= index <= characters.len(),
    ensures
        ipaddr_decimal_nat(
            input,
            start + index,
            end,
            accumulator,
        ) == ipaddr_decimal_nat(
            characters,
            index,
            characters.len() as int,
            accumulator,
        ),
    decreases characters.len() - index,
{
    if index < characters.len() {
        assert(input[start + index] == characters[index]);
        ipaddr_decimal_nat_slice(
            input,
            start,
            end,
            characters,
            index + 1,
            accumulator * 10 + ipaddr_digit_value(characters[index]),
        );
    }
    reveal(ipaddr_decimal_nat);
}

pub proof fn ipaddr_decimal_nat_accepted_digits(
    input: Seq<char>,
    index: int,
    end: int,
    accumulator: int,
    value: int,
)
    requires
        0 <= index <= end <= input.len(),
        0 <= accumulator,
        ipaddr_decimal_nat(input, index, end, accumulator)
            == Some(value),
    ensures
        forall|checked: int| index <= checked < end ==>
            #[trigger] ipaddr_is_digit(input[checked]),
        0 <= value,
    decreases end - index,
{
    reveal(ipaddr_decimal_nat);
    if index < end {
        assert(ipaddr_is_digit(input[index]));
        assert(0 <= ipaddr_digit_value(input[index])) by {
            reveal(ipaddr_is_digit);
            reveal(ipaddr_digit_value);
        }
        ipaddr_decimal_nat_accepted_digits(
            input,
            index + 1,
            end,
            accumulator * 10 + ipaddr_digit_value(input[index]),
            value,
        );
    }
}

#[verifier::spinoff_prover]
pub proof fn ipaddr_parse_prefix_sound(
    input: Seq<char>,
    start: int,
    end: int,
    maximum: int,
    value: int,
)
    requires
        0 <= start < end <= input.len(),
        0 <= maximum,
        ipaddr_parse_prefix(input, start, end, maximum) == Some(value),
    ensures
        ({
            let characters = input.subrange(start, end);
            let maximum_length: int = if maximum == 32 { 2 } else { 3 };
            &&& 1 <= characters.len() <= maximum_length
            &&& forall|index: int| 0 <= index < characters.len() ==>
                #[trigger] ipv4_spec::triptych_is_digit(characters[index])
            &&& (characters[0] != '0' || characters == seq!['0'])
            &&& 0 <= ipv4_spec::triptych_nat_of(characters) <= maximum
            &&& ipv4_spec::triptych_nat_of(characters) == value
        }),
{
    let characters = input.subrange(start, end);
    let maximum_length: int = if maximum == 32 { 2 } else { 3 };
    reveal(ipaddr_parse_prefix);
    assert(end - start <= maximum_length);
    assert(!(input[start] == '0' && end - start != 1));
    assert(ipaddr_decimal_nat(input, start, end, 0) == Some(value));
    assert(value <= maximum);
    ipaddr_decimal_nat_accepted_digits(input, start, end, 0, value);
    assert(characters.len() == end - start);
    assert forall|index: int| 0 <= index < characters.len() implies
        #[trigger] ipv4_spec::triptych_is_digit(characters[index]) by {
        assert(characters[index] == input[start + index]);
        assert(ipaddr_is_digit(input[start + index]));
        reveal(ipaddr_is_digit);
        reveal(ipv4_spec::triptych_is_digit);
    }
    assert(input[start] == characters[0]);
    assert(characters[0] != '0' || characters == seq!['0']) by {
        if characters[0] == '0' {
            assert(characters.len() == 1);
            assert_seqs_equal!(characters == seq!['0']);
        }
    }
    ipaddr_decimal_nat_slice(input, start, end, characters, 0, 0);
    ipv4_decimal_nat_matches(characters, 0, 0);
    assert(ipv4_spec::triptych_nat_of(characters) == value);
}

pub proof fn ipaddr_parse_prefix_slice(
    input: Seq<char>,
    start: int,
    end: int,
    characters: Seq<char>,
    maximum: int,
)
    requires
        0 <= start < end <= input.len(),
        input.subrange(start, end) == characters,
    ensures
        ipaddr_parse_prefix(input, start, end, maximum)
            == ipaddr_parse_prefix(
                characters,
                0,
                characters.len() as int,
                maximum,
            ),
{
    assert(input[start] == characters[0]);
    ipaddr_decimal_nat_slice(input, start, end, characters, 0, 0);
    reveal(ipaddr_parse_prefix);
}

pub proof fn ipaddr_ipv4_state_prefix_extensional(
    input: Seq<char>,
    prefix: Seq<char>,
    index: int,
    end: int,
    completed_segments: int,
    address: int,
    octet: int,
    digits: int,
)
    requires
        0 <= index <= end <= input.len(),
        end == prefix.len(),
        input.subrange(0, end) == prefix,
    ensures
        ipaddr_ipv4_state(
            input,
            index,
            end,
            completed_segments,
            address,
            octet,
            digits,
        ) == ipaddr_ipv4_state(
            prefix,
            index,
            end,
            completed_segments,
            address,
            octet,
            digits,
        ),
    decreases end - index,
{
    if index < end {
        assert(input[index] == prefix[index]);
        if ipaddr_is_digit(input[index]) {
            let next_octet =
                octet * 10 + ipaddr_digit_value(input[index]);
            if !(digits == 3
                || (0 < digits && octet == 0)
                || next_octet > 255)
            {
                ipaddr_ipv4_state_prefix_extensional(
                    input,
                    prefix,
                    index + 1,
                    end,
                    completed_segments,
                    address,
                    next_octet,
                    digits + 1,
                );
            }
        } else if input[index] == '.'
            && 0 < digits
            && completed_segments < 3
        {
            ipaddr_ipv4_state_prefix_extensional(
                input,
                prefix,
                index + 1,
                end,
                completed_segments + 1,
                address * 256 + octet,
                0,
                0,
            );
        }
    }
    reveal(ipaddr_ipv4_state);
}

pub proof fn ipaddr_contains_present(
    input: Seq<char>,
    start: int,
    end: int,
    witness: int,
    character: char,
)
    requires
        0 <= start <= witness < end <= input.len(),
        input[witness] == character,
    ensures
        ipaddr_contains(input, start, end, character),
    decreases witness - start,
{
    if start < witness {
        ipaddr_contains_present(
            input,
            start + 1,
            end,
            witness,
            character,
        );
    }
    reveal(ipaddr_contains);
}

pub proof fn ipaddr_excludes_concat(
    left: Seq<char>,
    right: Seq<char>,
    character: char,
)
    requires
        forall|index: int| 0 <= index < left.len() ==>
            #[trigger] left[index] != character,
        forall|index: int| 0 <= index < right.len() ==>
            #[trigger] right[index] != character,
    ensures
        forall|index: int| 0 <= index < (left + right).len() ==>
            #[trigger] (left + right)[index] != character,
{
    assert forall|index: int| 0 <= index < (left + right).len() implies
        #[trigger] (left + right)[index] != character by {
        if index < left.len() {
            assert((left + right)[index] == left[index]);
        } else {
            assert((left + right)[index] == right[index - left.len()]);
        }
    }
}

pub proof fn ipv4_digits_exclude(
    characters: Seq<char>,
    character: char,
)
    requires
        character == '/' || character == ':' || character == '.',
        forall|index: int| 0 <= index < characters.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(characters[index]),
    ensures
        forall|index: int| 0 <= index < characters.len() ==>
            #[trigger] characters[index] != character,
{
    assert forall|index: int| 0 <= index < characters.len() implies
        #[trigger] characters[index] != character by {
        assert(ipv4_spec::triptych_is_digit(characters[index]));
        reveal(ipv4_spec::triptych_is_digit);
    }
}

pub proof fn ipv4_address_excludes(
    oct1: Seq<char>,
    oct2: Seq<char>,
    oct3: Seq<char>,
    oct4: Seq<char>,
    character: char,
)
    requires
        character == '/' || character == ':',
        forall|index: int| 0 <= index < oct1.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct1[index]),
        forall|index: int| 0 <= index < oct2.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct2[index]),
        forall|index: int| 0 <= index < oct3.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct3[index]),
        forall|index: int| 0 <= index < oct4.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct4[index]),
    ensures
        forall|index: int|
            0 <= index
                < (oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.']
                    + oct4).len() ==>
                #[trigger] (oct1 + seq!['.'] + oct2 + seq!['.'] + oct3
                    + seq!['.'] + oct4)[index] != character,
{
    ipv4_digits_exclude(oct1, character);
    ipv4_digits_exclude(oct2, character);
    ipv4_digits_exclude(oct3, character);
    ipv4_digits_exclude(oct4, character);
    assert forall|index: int| 0 <= index < seq!['.'].len() implies
        #[trigger] seq!['.'][index] != character by {}
    ipaddr_excludes_concat(oct1, seq!['.'], character);
    ipaddr_excludes_concat(oct1 + seq!['.'], oct2, character);
    ipaddr_excludes_concat(
        oct1 + seq!['.'] + oct2,
        seq!['.'],
        character,
    );
    ipaddr_excludes_concat(
        oct1 + seq!['.'] + oct2 + seq!['.'],
        oct3,
        character,
    );
    ipaddr_excludes_concat(
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3,
        seq!['.'],
        character,
    );
    ipaddr_excludes_concat(
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'],
        oct4,
        character,
    );
}

#[verifier::spinoff_prover]
pub proof fn ipv4_consume_octet(
    input: Seq<char>,
    index: int,
    end: int,
    completed_segments: int,
    address: int,
    octet: Seq<char>,
)
    requires
        0 <= index,
        index + octet.len() <= end <= input.len(),
        0 <= completed_segments <= 3,
        0 <= address,
        input.subrange(index, index + octet.len() as int) == octet,
        1 <= octet.len() <= 3,
        forall|checked: int| 0 <= checked < octet.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(octet[checked]),
        octet[0] != '0' || octet == seq!['0'],
        0 <= ipv4_spec::triptych_nat_of(octet),
        ipv4_spec::triptych_nat_of(octet) <= 255,
    ensures
        ipaddr_ipv4_state(
            input,
            index,
            end,
            completed_segments,
            address,
            0,
            0,
        ) == ipaddr_ipv4_state(
            input,
            index + octet.len() as int,
            end,
            completed_segments,
            address,
            ipv4_spec::triptych_nat_of(octet),
            octet.len() as int,
        ),
{
    reveal(ipv4_spec::triptych_is_digit);
    reveal(ipaddr_is_digit);
    reveal(ipaddr_digit_value);
    reveal(ipv4_spec::triptych_nat_of);
    if octet.len() == 1 {
        assert(input[index] == octet[0]);
        assert(ipv4_spec::triptych_is_digit(octet[0]));
        assert(ipaddr_is_digit(input[index]));
        reveal_with_fuel(ipv4_spec::triptych_nat_of_from, 2);
        reveal_with_fuel(ipaddr_ipv4_state, 1);
    } else if octet.len() == 2 {
        assert(input[index] == octet[0]);
        assert(input[index + 1] == octet[1]);
        assert(ipv4_spec::triptych_is_digit(octet[0]));
        assert(ipv4_spec::triptych_is_digit(octet[1]));
        assert(ipaddr_is_digit(input[index]));
        assert(ipaddr_is_digit(input[index + 1]));
        assert(ipaddr_digit_value(input[index]) > 0);
        reveal_with_fuel(ipv4_spec::triptych_nat_of_from, 3);
        reveal_with_fuel(ipaddr_ipv4_state, 2);
    } else {
        assert(octet.len() == 3);
        assert(input[index] == octet[0]);
        assert(input[index + 1] == octet[1]);
        assert(input[index + 2] == octet[2]);
        assert(ipv4_spec::triptych_is_digit(octet[0]));
        assert(ipv4_spec::triptych_is_digit(octet[1]));
        assert(ipv4_spec::triptych_is_digit(octet[2]));
        assert(ipaddr_is_digit(input[index]));
        assert(ipaddr_is_digit(input[index + 1]));
        assert(ipaddr_is_digit(input[index + 2]));
        assert(ipaddr_digit_value(input[index]) > 0);
        reveal_with_fuel(ipv4_spec::triptych_nat_of_from, 4);
        reveal_with_fuel(ipaddr_ipv4_state, 3);
    }
}

#[verifier::spinoff_prover]
pub proof fn ipv4_octets_parse(
    oct1: Seq<char>,
    oct2: Seq<char>,
    oct3: Seq<char>,
    oct4: Seq<char>,
)
    requires
        1 <= oct1.len() <= 3,
        1 <= oct2.len() <= 3,
        1 <= oct3.len() <= 3,
        1 <= oct4.len() <= 3,
        forall|index: int| 0 <= index < oct1.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct1[index]),
        forall|index: int| 0 <= index < oct2.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct2[index]),
        forall|index: int| 0 <= index < oct3.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct3[index]),
        forall|index: int| 0 <= index < oct4.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct4[index]),
        oct1[0] != '0' || oct1 == seq!['0'],
        oct2[0] != '0' || oct2 == seq!['0'],
        oct3[0] != '0' || oct3 == seq!['0'],
        oct4[0] != '0' || oct4 == seq!['0'],
        0 <= ipv4_spec::triptych_nat_of(oct1),
        0 <= ipv4_spec::triptych_nat_of(oct2),
        0 <= ipv4_spec::triptych_nat_of(oct3),
        0 <= ipv4_spec::triptych_nat_of(oct4),
        ipv4_spec::triptych_nat_of(oct1) <= 255,
        ipv4_spec::triptych_nat_of(oct2) <= 255,
        ipv4_spec::triptych_nat_of(oct3) <= 255,
        ipv4_spec::triptych_nat_of(oct4) <= 255,
    ensures
        ipaddr_ipv4_state(
            oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'] + oct4,
            0,
            (oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'] + oct4).len()
                as int,
            0,
            0,
            0,
            0,
        ) == Some(
            ((ipv4_spec::triptych_nat_of(oct1) * 256
                + ipv4_spec::triptych_nat_of(oct2)) * 256
                + ipv4_spec::triptych_nat_of(oct3)) * 256
                + ipv4_spec::triptych_nat_of(oct4),
        ),
{
    let input =
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'] + oct4;
    let end = input.len() as int;
    let index1 = oct1.len() as int;
    let index2 = index1 + 1 + oct2.len() as int;
    let index3 = index2 + 1 + oct3.len() as int;
    let octet1 = ipv4_spec::triptych_nat_of(oct1);
    let octet2 = ipv4_spec::triptych_nat_of(oct2);
    let octet3 = ipv4_spec::triptych_nat_of(oct3);
    let octet4 = ipv4_spec::triptych_nat_of(oct4);

    assert(input.subrange(0, index1) == oct1) by {
        assert_seqs_equal!(input.subrange(0, index1) == oct1);
    }
    ipv4_consume_octet(input, 0, end, 0, 0, oct1);
    assert(input[index1] == '.');
    assert(!ipaddr_is_digit(input[index1])) by {
        reveal(ipaddr_is_digit);
    }
    assert(
        ipaddr_ipv4_state(input, index1, end, 0, 0, octet1, oct1.len() as int)
            == ipaddr_ipv4_state(
                input,
                index1 + 1,
                end,
                1,
                octet1,
                0,
                0,
            )
    ) by {
        reveal_with_fuel(ipaddr_ipv4_state, 1);
    }

    assert(
        input.subrange(index1 + 1, index2) == oct2
    ) by {
        assert_seqs_equal!(input.subrange(index1 + 1, index2) == oct2);
    }
    ipv4_consume_octet(input, index1 + 1, end, 1, octet1, oct2);
    assert(input[index2] == '.');
    assert(!ipaddr_is_digit(input[index2])) by {
        reveal(ipaddr_is_digit);
    }
    assert(
        ipaddr_ipv4_state(
            input,
            index2,
            end,
            1,
            octet1,
            octet2,
            oct2.len() as int,
        ) == ipaddr_ipv4_state(
            input,
            index2 + 1,
            end,
            2,
            octet1 * 256 + octet2,
            0,
            0,
        )
    ) by {
        reveal_with_fuel(ipaddr_ipv4_state, 1);
    }

    assert(
        input.subrange(index2 + 1, index3) == oct3
    ) by {
        assert_seqs_equal!(input.subrange(index2 + 1, index3) == oct3);
    }
    ipv4_consume_octet(
        input,
        index2 + 1,
        end,
        2,
        octet1 * 256 + octet2,
        oct3,
    );
    assert(input[index3] == '.');
    assert(!ipaddr_is_digit(input[index3])) by {
        reveal(ipaddr_is_digit);
    }
    assert(
        ipaddr_ipv4_state(
            input,
            index3,
            end,
            2,
            octet1 * 256 + octet2,
            octet3,
            oct3.len() as int,
        ) == ipaddr_ipv4_state(
            input,
            index3 + 1,
            end,
            3,
            (octet1 * 256 + octet2) * 256 + octet3,
            0,
            0,
        )
    ) by {
        reveal_with_fuel(ipaddr_ipv4_state, 1);
    }

    assert(
        input.subrange(index3 + 1, end) == oct4
    ) by {
        assert_seqs_equal!(input.subrange(index3 + 1, end) == oct4);
    }
    ipv4_consume_octet(
        input,
        index3 + 1,
        end,
        3,
        (octet1 * 256 + octet2) * 256 + octet3,
        oct4,
    );
    reveal_with_fuel(ipaddr_ipv4_state, 1);
}

#[verifier::spinoff_prover]
pub proof fn ipv4_prefix_parses(prefix: Seq<char>)
    requires
        1 <= prefix.len() <= 2,
        forall|index: int| 0 <= index < prefix.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(prefix[index]),
        prefix[0] != '0' || prefix == seq!['0'],
        ipv4_spec::triptych_nat_of(prefix) <= 32,
    ensures
        ipaddr_parse_prefix(prefix, 0, prefix.len() as int, 32)
            == Some(ipv4_spec::triptych_nat_of(prefix)),
{
    ipv4_decimal_nat_matches(prefix, 0, 0);
    reveal(ipv4_spec::triptych_nat_of);
    reveal(ipaddr_parse_prefix);
}

#[verifier::spinoff_prover]
pub proof fn ipv4_address_shape(
    oct1: Seq<char>,
    oct2: Seq<char>,
    oct3: Seq<char>,
    oct4: Seq<char>,
)
    requires
        1 <= oct1.len() <= 3,
        1 <= oct2.len() <= 3,
        1 <= oct3.len() <= 3,
        1 <= oct4.len() <= 3,
        forall|index: int| 0 <= index < oct1.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct1[index]),
        forall|index: int| 0 <= index < oct2.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct2[index]),
        forall|index: int| 0 <= index < oct3.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct3[index]),
        forall|index: int| 0 <= index < oct4.len() ==>
            #[trigger] ipv4_spec::triptych_is_digit(oct4[index]),
    ensures
        ({
            let address =
                oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'] + oct4;
            &&& is_ascii_chars(address)
            &&& ipaddr_find_slash(address, 0) == address.len()
            &&& ipaddr_contains(address, 0, address.len() as int, '.')
            &&& !ipaddr_contains(address, 0, address.len() as int, ':')
        }),
{
    let address =
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'] + oct4;
    ipv4_digit_sequence_ascii(oct1);
    ipv4_digit_sequence_ascii(oct2);
    ipv4_digit_sequence_ascii(oct3);
    ipv4_digit_sequence_ascii(oct4);
    assert(is_ascii_chars(seq!['.']));
    ipaddr_ascii_concat(oct1, seq!['.']);
    ipaddr_ascii_concat(oct1 + seq!['.'], oct2);
    ipaddr_ascii_concat(oct1 + seq!['.'] + oct2, seq!['.']);
    ipaddr_ascii_concat(oct1 + seq!['.'] + oct2 + seq!['.'], oct3);
    ipaddr_ascii_concat(
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3,
        seq!['.'],
    );
    ipaddr_ascii_concat(
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'],
        oct4,
    );
    assert(is_ascii_chars(address));
    ipv4_address_excludes(oct1, oct2, oct3, oct4, '/');
    ipv4_address_excludes(oct1, oct2, oct3, oct4, ':');
    ipaddr_find_slash_absent(address, 0);
    ipaddr_contains_absent(address, 0, address.len() as int, ':');
    assert(address[oct1.len() as int] == '.');
    ipaddr_contains_present(
        address,
        0,
        address.len() as int,
        oct1.len() as int,
        '.',
    );
}

#[verifier::spinoff_prover]
pub proof fn ipv4_generated_view_parses(
    input: Seq<char>,
    view: ipv4_spec::IPv4View,
)
    requires
        ipv4_spec::ipv4_matches_view(input, view),
        ipv4_spec::ipv4_view_valid(view),
    ensures
        match ipaddr_parse_spec(input) {
            Some(parsed) => {
                parsed.family == 4
                    && parsed.address * 33 + parsed.prefix
                        == ipv4_spec::ipv4_view_denotation(view)
            },
            None => false,
        },
{
    reveal(ipv4_spec::ipv4_matches_view);
    reveal(ipv4_spec::ipv4_matches_V4Net);
    reveal(ipv4_spec::ipv4_matches_V4Addr);
    reveal(ipv4_spec::ipv4_matches_Oct1);
    reveal(ipv4_spec::ipv4_matches_Oct2);
    reveal(ipv4_spec::ipv4_matches_Oct3);
    reveal(ipv4_spec::ipv4_matches_Oct4);
    reveal(ipv4_spec::ipv4_matches_Prefix);
    reveal(ipv4_spec::ipv4_view_valid);
    reveal(ipv4_spec::ipv4_view_wf_constraints);
    reveal(ipv4_spec::ipv4_wf_constraints);
    reveal(ipv4_spec::ipv4_view_denotation);
    reveal(ipv4_spec::ipv4_value);
    let oct1 = view.oct1;
    let oct2 = view.oct2;
    let oct3 = view.oct3;
    let oct4 = view.oct4;
    let prefix = view.prefix;
    let address =
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'] + oct4;

    ipv4_address_shape(oct1, oct2, oct3, oct4);
    ipv4_octets_parse(oct1, oct2, oct3, oct4);
    if prefix == seq![] {
        assert(input == address);
        assert(input.len() <= 15);
        reveal(ipaddr_parse_spec);
    } else {
        let address_end = address.len() as int;
        ipv4_prefix_parses(prefix);
        ipv4_digit_sequence_ascii(prefix);
        assert(input == address + seq!['/'] + prefix);
        assert(is_ascii_chars(seq!['/']));
        ipaddr_ascii_concat(address, seq!['/']);
        ipaddr_ascii_concat(address + seq!['/'], prefix);
        assert(is_ascii_chars(input));
        assert(input.len() <= 18);
        assert(input.subrange(0, address_end) == address) by {
            assert_seqs_equal!(input.subrange(0, address_end) == address);
        }
        assert(input[address_end] == '/');
        assert forall|index: int| 0 <= index < address_end implies
            #[trigger] input[index] != '/' by {
            assert(input[index] == address[index]);
        }
        ipaddr_find_slash_after_prefix(input, address_end, 0);
        ipaddr_contains_prefix_extensional(
            input,
            address,
            0,
            address_end,
            '.',
        );
        ipaddr_contains_prefix_extensional(
            input,
            address,
            0,
            address_end,
            ':',
        );
        ipaddr_ipv4_state_prefix_extensional(
            input,
            address,
            0,
            address_end,
            0,
            0,
            0,
            0,
        );
        assert(
            input.subrange(address_end + 1, input.len() as int)
                == prefix
        ) by {
            assert_seqs_equal!(
                input.subrange(address_end + 1, input.len() as int)
                    == prefix
            );
        }
        ipaddr_parse_prefix_slice(
            input,
            address_end + 1,
            input.len() as int,
            prefix,
            32,
        );
        reveal(ipaddr_parse_spec);
    }
}

#[verifier::rlimit(250)]
pub proof fn ipv6_generated_view_parses(
    input: Seq<char>,
    view: ipv6_spec::IPv6View,
)
    requires
        ipv6_spec::ipv6_matches_view(input, view),
        ipv6_spec::ipv6_view_wf_constraints(view),
    ensures
        match ipaddr_parse_spec(input) {
            Some(parsed) => {
                parsed.family == 6
                    && parsed.address * 129 + parsed.prefix
                        == ipv6_spec::ipv6_view_denotation(view)
            },
            None => false,
        },
{
    reveal(ipv6_spec::ipv6_matches_view);
    reveal(ipv6_spec::ipv6_matches_V6Net);
    reveal(ipv6_spec::ipv6_view_wf_constraints);
    reveal(ipv6_spec::ipv6_wf_constraints);
    reveal(ipv6_spec::ipv6_view_denotation);
    reveal(ipv6_spec::ipv6_value);
    let empty = Seq::<char>::empty();
    if exists|v6_addr: Seq<char>|
        input == v6_addr
            && #[trigger] ipv6_spec::ipv6_matches_V6Addr(
                v6_addr,
                view,
            )
            && view.prefix == seq![]
    {
        let address = choose|v6_addr: Seq<char>|
            input == v6_addr
                && #[trigger] ipv6_spec::ipv6_matches_V6Addr(
                    v6_addr,
                    view,
                )
                && view.prefix == seq![];
        assert(input == address);
        assert(view.prefix == empty);
        ipv6_generated_address_parses(address, view);
        let colon_index = choose|index: int|
            0 <= index < address.len() && address[index] == ':';
        ipaddr_find_slash_absent(address, 0);
        ipaddr_contains_present(
            address,
            0,
            address.len() as int,
            colon_index,
            ':',
        );
        ipaddr_contains_absent(
            address,
            0,
            address.len() as int,
            '.',
        );
        assert(address.len() > 0);
        reveal(ipaddr_parse_spec);
    } else {
        let (address, prefix) =
            choose|v6_addr: Seq<char>, prefix: Seq<char>|
                input == v6_addr + seq!['/'] + prefix
                    && #[trigger] ipv6_spec::ipv6_matches_V6Addr(
                        v6_addr,
                        view,
                    )
                    && view.prefix == prefix
                    && #[trigger] ipv6_spec::ipv6_matches_Prefix(
                        prefix,
                        view,
                    );
        assert(input == address + seq!['/'] + prefix);
        assert(view.prefix == prefix);
        ipv6_generated_address_parses(address, view);
        reveal(ipv6_spec::ipv6_matches_Prefix);
        assert(1 <= prefix.len() <= 3);
        assert forall|index: int| 0 <= index < prefix.len() implies
            #[trigger] ipv6_spec::triptych_is_digit(
                prefix[index],
            ) by {}
        assert(prefix[0] != '0' || prefix == seq!['0']);
        assert(
            0 <= ipv6_spec::triptych_nat_of(prefix) <= 128
        );
        ipv6_prefix_parses(prefix);
        assert(ipv6_address_alphabet(prefix)) by {
            reveal(ipv6_address_alphabet);
            assert forall|index: int| 0 <= index < prefix.len() implies
                #[trigger] ipv6_spec::triptych_is_hex_digit(
                    prefix[index],
                ) || prefix[index] == ':' by {
                assert(ipv6_spec::triptych_is_digit(prefix[index]));
                reveal(ipv6_spec::triptych_is_hex_digit);
            }
        }
        ipv6_alphabet_ascii(prefix);
        assert(is_ascii_chars(seq!['/']));
        ipaddr_ascii_concat(address, seq!['/']);
        ipaddr_ascii_concat(address + seq!['/'], prefix);
        assert(is_ascii_chars(input));
        assert(input.len() <= 43);
        let address_end = address.len() as int;
        assert(
            input.subrange(0, address_end) == address
        ) by {
            assert_seqs_equal!(
                input.subrange(0, address_end) == address
            );
        }
        assert(input[address_end] == '/');
        assert forall|index: int| 0 <= index < address_end implies
            #[trigger] input[index] != '/' by {
            assert(input[index] == address[index]);
        }
        ipaddr_find_slash_after_prefix(input, address_end, 0);
        let colon_index = choose|index: int|
            0 <= index < address.len() && address[index] == ':';
        ipaddr_contains_present(
            address,
            0,
            address_end,
            colon_index,
            ':',
        );
        ipaddr_contains_absent(
            address,
            0,
            address_end,
            '.',
        );
        ipaddr_contains_prefix_extensional(
            input,
            address,
            0,
            address_end,
            ':',
        );
        ipaddr_contains_prefix_extensional(
            input,
            address,
            0,
            address_end,
            '.',
        );
        ipaddr_ipv6_state_prefix_extensional(
            input,
            address,
            0,
            0,
            address_end,
            0,
            0,
            0,
            0,
            false,
            0,
            0,
        );
        assert(
            input.subrange(address_end + 1, input.len() as int)
                == prefix
        ) by {
            assert_seqs_equal!(
                input.subrange(
                    address_end + 1,
                    input.len() as int,
                ) == prefix
            );
        }
        ipaddr_parse_prefix_slice(
            input,
            address_end + 1,
            input.len() as int,
            prefix,
            128,
        );
        assert(address.len() > 0);
        reveal(ipaddr_parse_spec);
    }
}

pub proof fn ipv6_valid_has_result(input: Seq<char>)
    requires
        ipv6_spec::ipv6_is_valid(input),
    ensures
        exists|value: int|
            crate::ipv6::contract::ipv6_matches_result(
                input,
                value,
            ),
{
    reveal(ipv6_spec::ipv6_is_valid);
    reveal(ipv6_spec::ipv6_is_wf);
    reveal(ipv6_spec::ipv6_satisfies_wf_constraints);
    let view = choose|view: ipv6_spec::IPv6View|
        ipv6_spec::ipv6_matches_view(input, view)
            && #[trigger] ipv6_spec::ipv6_view_wf_constraints(view);
    ipv6_generated_view_parses(input, view);
    match ipaddr_parse_spec(input) {
        Some(parsed) => {
            assert(parsed.family == 6);
            ipv6_parse_spec_sound(
                input,
                parsed.address,
                parsed.prefix,
            );
            assert(exists|value: int|
                crate::ipv6::contract::ipv6_matches_result(
                    input,
                    value,
                )) by {
                assert(
                    crate::ipv6::contract::ipv6_matches_result(
                        input,
                        parsed.address * 129 + parsed.prefix,
                    )
                );
            }
        },
        None => {
            assert(false);
        },
    }
}

impl IPv4ExternalParserContract for IpAddrParser {
    open spec fn parse_to_spec(input: Seq<char>) -> Option<int> {
        match ipaddr_parse_spec(input) {
            Some(parsed) => {
                if parsed.family == 4 {
                    Some(parsed.address * 33 + parsed.prefix)
                } else {
                    None
                }
            },
            None => None,
        }
    }

    proof fn extparse_sound(input: Seq<char>, value: int) {
        match ipaddr_parse_spec(input) {
            Some(parsed) => {
                assert(parsed.family == 4);
                assert(parsed.address * 33 + parsed.prefix == value);
                ipv4_parse_spec_sound(
                    input,
                    parsed.address,
                    parsed.prefix,
                );
            },
            None => {
                assert(false);
            },
        }
    }

    proof fn extparse_complete(input: Seq<char>, value: int) {
        reveal(crate::ipv4::contract::ipv4_matches_result);
        let view = choose|view: ipv4_spec::IPv4View|
            ipv4_spec::ipv4_matches_view(input, view)
                && ipv4_spec::ipv4_view_valid(view)
                && ipv4_spec::ipv4_view_denotation(view) == value;
        ipv4_generated_view_parses(input, view);
    }

    proof fn extparse_reject(input: Seq<char>) {
        if <IpAddrParser as IPv4ExternalParserContract>::parse_to_spec(
            input,
        ).is_none() {
            if ipv4_is_valid(input) {
                ipv4_valid_has_result(input);
                let value = choose|value: int|
                    crate::ipv4::contract::ipv4_matches_result(
                        input,
                        value,
                    );
                <IpAddrParser as IPv4ExternalParserContract>::
                    extparse_complete(input, value);
                assert(false);
            }
        }
        if !ipv4_is_valid(input) {
            match <IpAddrParser as IPv4ExternalParserContract>::
                parse_to_spec(input)
            {
                Some(value) => {
                    <IpAddrParser as IPv4ExternalParserContract>::
                        extparse_sound(input, value);
                    assert(false);
                },
                None => {},
            }
        }
    }

    open spec fn to_string_to_spec(value: int) -> Seq<char> {
        ipv4_canonical_characters(value)
    }

    proof fn extparse_to_string_roundtrip(value: int) {
        ipv4_canonical_matches_result(value);
        <IpAddrParser as IPv4ExternalParserContract>::extparse_complete(
            ipv4_canonical_characters(value),
            value,
        );
    }

    proof fn extparse_to_string_injective(left: int, right: int) {
        <IpAddrParser as IPv4ExternalParserContract>::extparse_to_string_roundtrip(left);
        <IpAddrParser as IPv4ExternalParserContract>::extparse_to_string_roundtrip(right);
    }

    proof fn extparse_normalize_eq_iff_parse_eq(left: Seq<char>, right: Seq<char>) {
        match <IpAddrParser as IPv4ExternalParserContract>::parse_to_spec(left) {
            Some(left_value) => {
                <IpAddrParser as IPv4ExternalParserContract>::extparse_sound(
                    left,
                    left_value,
                );
                assert(crate::ipv4::contract::ipv4_has_result(left_value)) by {
                    reveal(crate::ipv4::contract::ipv4_has_result);
                    assert(crate::ipv4::contract::ipv4_matches_result(
                        left,
                        left_value,
                    ));
                }
                match <IpAddrParser as IPv4ExternalParserContract>::parse_to_spec(right) {
                    Some(right_value) => {
                        <IpAddrParser as IPv4ExternalParserContract>::extparse_sound(
                            right,
                            right_value,
                        );
                        assert(crate::ipv4::contract::ipv4_has_result(right_value)) by {
                            reveal(crate::ipv4::contract::ipv4_has_result);
                            assert(crate::ipv4::contract::ipv4_matches_result(
                                right,
                                right_value,
                            ));
                        }
                        if ipv4_canonical_characters(left_value)
                            == ipv4_canonical_characters(right_value) {
                            <IpAddrParser as IPv4ExternalParserContract>::
                                extparse_to_string_injective(
                                    left_value,
                                    right_value,
                                );
                        }
                    },
                    None => {},
                }
            },
            None => {},
        }
    }
}

impl IPv6ExternalParserContract for IpAddrParser {
    open spec fn parse_to_spec(input: Seq<char>) -> Option<int> {
        match ipaddr_parse_spec(input) {
            Some(parsed) => {
                if parsed.family == 6 {
                    Some(parsed.address * 129 + parsed.prefix)
                } else {
                    None
                }
            },
            None => None,
        }
    }

    proof fn extparse_sound(input: Seq<char>, value: int) {
        match ipaddr_parse_spec(input) {
            Some(parsed) => {
                assert(parsed.family == 6);
                assert(
                    parsed.address * 129 + parsed.prefix == value
                );
                ipv6_parse_spec_sound(
                    input,
                    parsed.address,
                    parsed.prefix,
                );
            },
            None => {
                assert(false);
            },
        }
    }

    proof fn extparse_complete(input: Seq<char>, value: int) {
        reveal(crate::ipv6::contract::ipv6_matches_result);
        let view = choose|view: ipv6_spec::IPv6View|
            ipv6_spec::ipv6_matches_view(input, view)
                && ipv6_spec::ipv6_view_valid(view)
                && ipv6_spec::ipv6_view_denotation(view) == value;
        reveal(ipv6_spec::ipv6_view_valid);
        ipv6_generated_view_parses(input, view);
    }

    proof fn extparse_reject(input: Seq<char>) {
        if <IpAddrParser as IPv6ExternalParserContract>::parse_to_spec(
            input,
        ).is_none() {
            if ipv6_is_valid(input) {
                ipv6_valid_has_result(input);
                let value = choose|value: int|
                    crate::ipv6::contract::ipv6_matches_result(
                        input,
                        value,
                    );
                <IpAddrParser as IPv6ExternalParserContract>::
                    extparse_complete(input, value);
                assert(false);
            }
        }
        if !ipv6_is_valid(input) {
            match <IpAddrParser as IPv6ExternalParserContract>::
                parse_to_spec(input)
            {
                Some(value) => {
                    <IpAddrParser as IPv6ExternalParserContract>::
                        extparse_sound(input, value);
                    assert(false);
                },
                None => {},
            }
        }
    }

    open spec fn to_string_to_spec(value: int) -> Seq<char> {
        ipv6_canonical_characters(value)
    }

    proof fn extparse_to_string_roundtrip(value: int) {
        ipv6_canonical_matches_result(value);
        <IpAddrParser as IPv6ExternalParserContract>::extparse_complete(
            ipv6_canonical_characters(value),
            value,
        );
    }

    proof fn extparse_to_string_injective(left: int, right: int) {
        <IpAddrParser as IPv6ExternalParserContract>::extparse_to_string_roundtrip(left);
        <IpAddrParser as IPv6ExternalParserContract>::extparse_to_string_roundtrip(right);
    }

    proof fn extparse_normalize_eq_iff_parse_eq(left: Seq<char>, right: Seq<char>) {
        match <IpAddrParser as IPv6ExternalParserContract>::parse_to_spec(left) {
            Some(left_value) => {
                <IpAddrParser as IPv6ExternalParserContract>::extparse_sound(
                    left,
                    left_value,
                );
                assert(crate::ipv6::contract::ipv6_has_result(left_value)) by {
                    reveal(crate::ipv6::contract::ipv6_has_result);
                    assert(crate::ipv6::contract::ipv6_matches_result(
                        left,
                        left_value,
                    ));
                }
                match <IpAddrParser as IPv6ExternalParserContract>::parse_to_spec(right) {
                    Some(right_value) => {
                        <IpAddrParser as IPv6ExternalParserContract>::extparse_sound(
                            right,
                            right_value,
                        );
                        assert(crate::ipv6::contract::ipv6_has_result(right_value)) by {
                            reveal(crate::ipv6::contract::ipv6_has_result);
                            assert(crate::ipv6::contract::ipv6_matches_result(
                                right,
                                right_value,
                            ));
                        }
                        if ipv6_canonical_characters(left_value)
                            == ipv6_canonical_characters(right_value) {
                            <IpAddrParser as IPv6ExternalParserContract>::
                                extparse_to_string_injective(
                                    left_value,
                                    right_value,
                                );
                        }
                    },
                    None => {},
                }
            },
            None => {},
        }
    }
}

} // verus!
