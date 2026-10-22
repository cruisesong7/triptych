#[cfg(verus_only)]
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_pos_bound,
};
#[cfg(verus_only)]
use vstd::arithmetic::mul::lemma_mul_is_associative;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::assert_seqs_equal;

#[cfg(verus_only)]
use crate::ipv4::contract::{ipv4_has_result, ipv4_matches_result};
#[cfg(verus_only)]
use crate::ipv4::spec as ipv4_spec;
#[cfg(verus_only)]
use crate::ipv6::contract::{ipv6_has_result, ipv6_matches_result};
#[cfg(verus_only)]
use crate::ipv6::spec as ipv6_spec;

verus! {

pub open spec fn ipv4_address_space() -> int {
    4_294_967_296int
}

pub open spec fn ipv6_address_space() -> int {
    340_282_366_920_938_463_463_374_607_431_768_211_455int + 1
}

pub open spec fn ipaddr_decimal_digit_character(digit: nat) -> char
    recommends
        digit <= 9,
{
    if digit == 0 {
        '0'
    } else if digit == 1 {
        '1'
    } else if digit == 2 {
        '2'
    } else if digit == 3 {
        '3'
    } else if digit == 4 {
        '4'
    } else if digit == 5 {
        '5'
    } else if digit == 6 {
        '6'
    } else if digit == 7 {
        '7'
    } else if digit == 8 {
        '8'
    } else {
        '9'
    }
}

fn ipaddr_decimal_digit_character_exec(digit: u16) -> (result: char)
    requires
        digit <= 9,
    ensures
        result == ipaddr_decimal_digit_character(digit as nat),
{
    if digit == 0 {
        '0'
    } else if digit == 1 {
        '1'
    } else if digit == 2 {
        '2'
    } else if digit == 3 {
        '3'
    } else if digit == 4 {
        '4'
    } else if digit == 5 {
        '5'
    } else if digit == 6 {
        '6'
    } else if digit == 7 {
        '7'
    } else if digit == 8 {
        '8'
    } else {
        '9'
    }
}

/** Minimal decimal rendering for values used by IP octets and prefixes. */
pub open spec fn ipaddr_decimal_characters(value: nat) -> Seq<char>
    recommends
        value <= 999,
{
    if value < 10 {
        seq![ipaddr_decimal_digit_character(value)]
    } else if value < 100 {
        seq![
            ipaddr_decimal_digit_character(value / 10),
            ipaddr_decimal_digit_character(value % 10),
        ]
    } else {
        seq![
            ipaddr_decimal_digit_character(value / 100),
            ipaddr_decimal_digit_character((value / 10) % 10),
            ipaddr_decimal_digit_character(value % 10),
        ]
    }
}

pub proof fn ipv4_decimal_characters_properties(value: nat)
    requires
        value <= 999,
    ensures
        1 <= ipaddr_decimal_characters(value).len() <= 3,
        forall|index: int|
            0 <= index < ipaddr_decimal_characters(value).len() ==>
                #[trigger] ipv4_spec::triptych_is_digit(
                    ipaddr_decimal_characters(value)[index],
                ),
        ipv4_spec::triptych_nat_of(ipaddr_decimal_characters(value)) == value,
        ipaddr_decimal_characters(value)[0] != '0'
            || ipaddr_decimal_characters(value) == seq!['0'],
{
    lemma_mod_pos_bound(value as int, 10);
    lemma_mod_pos_bound((value / 10) as int, 10);
    lemma_fundamental_div_mod(value as int, 10);
    lemma_fundamental_div_mod((value / 10) as int, 10);
    reveal(ipaddr_decimal_characters);
    reveal(ipaddr_decimal_digit_character);
    reveal(ipv4_spec::triptych_is_digit);
    reveal(ipv4_spec::triptych_nat_of);
    reveal_with_fuel(ipv4_spec::triptych_nat_of_from, 4);
    if value < 10 {
        if value == 0 {
        } else {
            assert(ipaddr_decimal_digit_character(value) != '0');
        }
    } else if value < 100 {
        assert(1 <= value / 10 <= 9);
        assert(ipaddr_decimal_digit_character(value / 10) != '0');
    } else {
        assert(1 <= value / 100 <= 9);
        assert(ipaddr_decimal_digit_character(value / 100) != '0');
    }
}

pub proof fn ipv6_decimal_characters_properties(value: nat)
    requires
        value <= 999,
    ensures
        1 <= ipaddr_decimal_characters(value).len() <= 3,
        forall|index: int|
            0 <= index < ipaddr_decimal_characters(value).len() ==>
                #[trigger] ipv6_spec::triptych_is_digit(
                    ipaddr_decimal_characters(value)[index],
                ),
        ipv6_spec::triptych_nat_of(ipaddr_decimal_characters(value)) == value,
        ipaddr_decimal_characters(value)[0] != '0'
            || ipaddr_decimal_characters(value) == seq!['0'],
{
    lemma_mod_pos_bound(value as int, 10);
    lemma_mod_pos_bound((value / 10) as int, 10);
    lemma_fundamental_div_mod(value as int, 10);
    lemma_fundamental_div_mod((value / 10) as int, 10);
    reveal(ipaddr_decimal_characters);
    reveal(ipaddr_decimal_digit_character);
    reveal(ipv6_spec::triptych_is_digit);
    reveal(ipv6_spec::triptych_nat_of);
    reveal_with_fuel(ipv6_spec::triptych_nat_of_from, 4);
    if value < 10 {
        if value == 0 {
        } else {
            assert(ipaddr_decimal_digit_character(value) != '0');
        }
    } else if value < 100 {
        assert(1 <= value / 10 <= 9);
        assert(ipaddr_decimal_digit_character(value / 10) != '0');
    } else {
        assert(1 <= value / 100 <= 9);
        assert(ipaddr_decimal_digit_character(value / 100) != '0');
    }
}

fn ipaddr_push_decimal(output: &mut String, value: u16)
    requires
        value <= 999,
    ensures
        final(output)@ == old(output)@ + ipaddr_decimal_characters(value as nat),
{
    if value < 10 {
        output.push(ipaddr_decimal_digit_character_exec(value));
    } else if value < 100 {
        let tens = value / 10;
        let ones = value % 10;
        proof {
            lemma_mod_pos_bound(value as int, 10);
            reveal(ipaddr_decimal_characters);
        }
        output.push(ipaddr_decimal_digit_character_exec(tens));
        output.push(ipaddr_decimal_digit_character_exec(ones));
    } else {
        let hundreds = value / 100;
        let tens = (value / 10) % 10;
        let ones = value % 10;
        proof {
            lemma_mod_pos_bound((value / 10) as int, 10);
            lemma_mod_pos_bound(value as int, 10);
            reveal(ipaddr_decimal_characters);
        }
        output.push(ipaddr_decimal_digit_character_exec(hundreds));
        output.push(ipaddr_decimal_digit_character_exec(tens));
        output.push(ipaddr_decimal_digit_character_exec(ones));
    }
}

pub open spec fn ipaddr_hex_digit_character(digit: nat) -> char
    recommends
        digit <= 15,
{
    if digit == 0 {
        '0'
    } else if digit == 1 {
        '1'
    } else if digit == 2 {
        '2'
    } else if digit == 3 {
        '3'
    } else if digit == 4 {
        '4'
    } else if digit == 5 {
        '5'
    } else if digit == 6 {
        '6'
    } else if digit == 7 {
        '7'
    } else if digit == 8 {
        '8'
    } else if digit == 9 {
        '9'
    } else if digit == 10 {
        'a'
    } else if digit == 11 {
        'b'
    } else if digit == 12 {
        'c'
    } else if digit == 13 {
        'd'
    } else if digit == 14 {
        'e'
    } else {
        'f'
    }
}

fn ipaddr_hex_digit_character_exec(digit: u16) -> (result: char)
    requires
        digit <= 15,
    ensures
        result == ipaddr_hex_digit_character(digit as nat),
{
    if digit == 0 {
        '0'
    } else if digit == 1 {
        '1'
    } else if digit == 2 {
        '2'
    } else if digit == 3 {
        '3'
    } else if digit == 4 {
        '4'
    } else if digit == 5 {
        '5'
    } else if digit == 6 {
        '6'
    } else if digit == 7 {
        '7'
    } else if digit == 8 {
        '8'
    } else if digit == 9 {
        '9'
    } else if digit == 10 {
        'a'
    } else if digit == 11 {
        'b'
    } else if digit == 12 {
        'c'
    } else if digit == 13 {
        'd'
    } else if digit == 14 {
        'e'
    } else {
        'f'
    }
}

/** Cedar-spec canonical IPv6 hextet: four lowercase hexadecimal digits. */
pub open spec fn ipaddr_hex4_characters(value: nat) -> Seq<char>
    recommends
        value < 65_536,
{
    seq![
        ipaddr_hex_digit_character(value / 4_096),
        ipaddr_hex_digit_character((value / 256) % 16),
        ipaddr_hex_digit_character((value / 16) % 16),
        ipaddr_hex_digit_character(value % 16),
    ]
}

pub proof fn ipv6_hex_digit_character_properties(digit: nat)
    requires
        digit <= 15,
    ensures
        ipv6_spec::triptych_is_hex_digit(ipaddr_hex_digit_character(digit)),
        ipv6_spec::triptych_hex_digit_value(ipaddr_hex_digit_character(digit)) == digit,
{
    reveal(ipaddr_hex_digit_character);
    reveal(ipv6_spec::triptych_is_hex_digit);
    reveal(ipv6_spec::triptych_is_digit);
    reveal(ipv6_spec::triptych_hex_digit_value);
}

pub proof fn ipv6_hex4_characters_wf(value: nat)
    requires
        value < 65_536,
    ensures
        ipaddr_hex4_characters(value).len() == 4,
        forall|index: int|
            0 <= index < 4 ==>
                #[trigger] ipv6_spec::triptych_is_hex_digit(
                    ipaddr_hex4_characters(value)[index],
                ),
{
    lemma_mod_pos_bound(value as int, 16);
    lemma_mod_pos_bound((value / 16) as int, 16);
    lemma_mod_pos_bound((value / 256) as int, 16);
    ipv6_hex_digit_character_properties(value / 4_096);
    ipv6_hex_digit_character_properties((value / 256) % 16);
    ipv6_hex_digit_character_properties((value / 16) % 16);
    ipv6_hex_digit_character_properties(value % 16);
    reveal(ipaddr_hex4_characters);
    assert forall|index: int| 0 <= index < 4 implies
        #[trigger] ipv6_spec::triptych_is_hex_digit(
            ipaddr_hex4_characters(value)[index],
        ) by {
        if index == 0 {
        } else if index == 1 {
        } else if index == 2 {
        } else {
            assert(index == 3);
        }
    }
}

pub proof fn ipv6_hex4_characters_value(value: nat)
    requires
        value < 65_536,
    ensures
        ipv6_spec::triptych_hex_seq_of(ipaddr_hex4_characters(value)) == value,
{
    lemma_mod_pos_bound(value as int, 16);
    lemma_mod_pos_bound((value / 16) as int, 16);
    lemma_mod_pos_bound((value / 256) as int, 16);
    lemma_fundamental_div_mod(value as int, 16);
    lemma_fundamental_div_mod((value / 16) as int, 16);
    lemma_fundamental_div_mod((value / 256) as int, 16);
    lemma_fundamental_div_mod((value / 4_096) as int, 16);
    ipv6_hex_digit_character_properties(value / 4_096);
    ipv6_hex_digit_character_properties((value / 256) % 16);
    ipv6_hex_digit_character_properties((value / 16) % 16);
    ipv6_hex_digit_character_properties(value % 16);
    reveal(ipaddr_hex4_characters);
    reveal(ipv6_spec::triptych_hex_seq_of);
    reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 5);
}

pub proof fn ipv6_hex4_characters_properties(value: nat)
    requires
        value < 65_536,
    ensures
        ipaddr_hex4_characters(value).len() == 4,
        forall|index: int|
            0 <= index < 4 ==>
                #[trigger] ipv6_spec::triptych_is_hex_digit(
                    ipaddr_hex4_characters(value)[index],
                ),
        ipv6_spec::triptych_hex_seq_of(ipaddr_hex4_characters(value)) == value,
{
    ipv6_hex4_characters_wf(value);
    ipv6_hex4_characters_value(value);
}

pub proof fn ipv6_hex_seq_from_concat_suffix(
    prefix: Seq<char>,
    suffix: Seq<char>,
    index: int,
    accumulator: int,
    current: int,
)
    requires
        0 <= index <= suffix.len(),
    ensures
        ipv6_spec::triptych_hex_seq_from(
            prefix + suffix,
            prefix.len() as int + index,
            accumulator,
            current,
        ) == ipv6_spec::triptych_hex_seq_from(
            suffix,
            index,
            accumulator,
            current,
        ),
    decreases suffix.len() - index,
{
    if index < suffix.len() {
        assert(
            (prefix + suffix)[prefix.len() as int + index] == suffix[index]
        );
        if suffix[index] == ':' {
            ipv6_hex_seq_from_concat_suffix(
                prefix,
                suffix,
                index + 1,
                accumulator * 65_536 + current,
                0,
            );
        } else {
            ipv6_hex_seq_from_concat_suffix(
                prefix,
                suffix,
                index + 1,
                accumulator,
                current * 16
                    + ipv6_spec::triptych_hex_digit_value(suffix[index]),
            );
        }
        reveal(ipv6_spec::triptych_hex_seq_from);
    } else {
        reveal(ipv6_spec::triptych_hex_seq_from);
    }
}

pub proof fn ipv6_hex4_from_initial(
    value: nat,
    accumulator: int,
)
    requires
        value < 65_536,
    ensures
        ipv6_spec::triptych_hex_seq_from(
            ipaddr_hex4_characters(value),
            0,
            accumulator,
            0,
        ) == accumulator * 65_536 + value,
{
    lemma_mod_pos_bound(value as int, 16);
    lemma_mod_pos_bound((value / 16) as int, 16);
    lemma_mod_pos_bound((value / 256) as int, 16);
    lemma_fundamental_div_mod(value as int, 16);
    lemma_fundamental_div_mod((value / 16) as int, 16);
    lemma_fundamental_div_mod((value / 256) as int, 16);
    lemma_fundamental_div_mod((value / 4_096) as int, 16);
    ipv6_hex_digit_character_properties(value / 4_096);
    ipv6_hex_digit_character_properties((value / 256) % 16);
    ipv6_hex_digit_character_properties((value / 16) % 16);
    ipv6_hex_digit_character_properties(value % 16);
    reveal(ipaddr_hex4_characters);
    reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 5);
}

pub proof fn ipv6_hex_seq_append_group(
    prefix: Seq<char>,
    index: int,
    accumulator: int,
    current: int,
    group: nat,
)
    requires
        0 <= index <= prefix.len(),
        group < 65_536,
    ensures
        ipv6_spec::triptych_hex_seq_from(
            prefix + seq![':'] + ipaddr_hex4_characters(group),
            index,
            accumulator,
            current,
        ) == ipv6_spec::triptych_hex_seq_from(
            prefix,
            index,
            accumulator,
            current,
        ) * 65_536 + group,
    decreases prefix.len() - index,
{
    if index < prefix.len() {
        assert(
            (prefix + seq![':'] + ipaddr_hex4_characters(group))[index]
                == prefix[index]
        );
        if prefix[index] == ':' {
            ipv6_hex_seq_append_group(
                prefix,
                index + 1,
                accumulator * 65_536 + current,
                0,
                group,
            );
        } else {
            ipv6_hex_seq_append_group(
                prefix,
                index + 1,
                accumulator,
                current * 16
                    + ipv6_spec::triptych_hex_digit_value(prefix[index]),
                group,
            );
        }
        reveal(ipv6_spec::triptych_hex_seq_from);
    } else {
        let suffix = seq![':'] + ipaddr_hex4_characters(group);
        assert(
            prefix + seq![':'] + ipaddr_hex4_characters(group)
                == prefix + suffix
        );
        ipv6_hex_seq_from_concat_suffix(
            prefix,
            suffix,
            0,
            accumulator,
            current,
        );
        assert(suffix[0] == ':');
        reveal_with_fuel(ipv6_spec::triptych_hex_seq_from, 2);
        ipv6_hex_seq_from_concat_suffix(
            seq![':'],
            ipaddr_hex4_characters(group),
            0,
            accumulator * 65_536 + current,
            0,
        );
        ipv6_hex4_from_initial(
            group,
            accumulator * 65_536 + current,
        );
    }
}

fn ipaddr_push_hex4(output: &mut String, value: u16)
    ensures
        final(output)@ == old(output)@ + ipaddr_hex4_characters(value as nat),
{
    let first = value / 4_096;
    let second = (value / 256) % 16;
    let third = (value / 16) % 16;
    let fourth = value % 16;
    proof {
        lemma_mod_pos_bound((value / 256) as int, 16);
        lemma_mod_pos_bound((value / 16) as int, 16);
        lemma_mod_pos_bound(value as int, 16);
        reveal(ipaddr_hex4_characters);
    }
    output.push(ipaddr_hex_digit_character_exec(first));
    output.push(ipaddr_hex_digit_character_exec(second));
    output.push(ipaddr_hex_digit_character_exec(third));
    output.push(ipaddr_hex_digit_character_exec(fourth));
}

pub open spec fn ipv4_canonical_characters(value: int) -> Seq<char>
    recommends
        0 <= value < ipv4_address_space() * 33,
{
    let address = value / 33;
    let prefix = value % 33;
    let quotient1 = address / 256;
    let quotient2 = quotient1 / 256;
    let quotient3 = quotient2 / 256;
    ipaddr_decimal_characters((quotient3 % 256) as nat)
        + seq!['.']
        + ipaddr_decimal_characters((quotient2 % 256) as nat)
        + seq!['.']
        + ipaddr_decimal_characters((quotient1 % 256) as nat)
        + seq!['.']
        + ipaddr_decimal_characters((address % 256) as nat)
        + seq!['/']
        + ipaddr_decimal_characters(prefix as nat)
}

pub open spec fn ipv6_full_characters(address: int) -> Seq<char>
    recommends
        0 <= address < ipv6_address_space(),
{
    let quotient1 = address / 65_536;
    let quotient2 = quotient1 / 65_536;
    let quotient3 = quotient2 / 65_536;
    let quotient4 = quotient3 / 65_536;
    let quotient5 = quotient4 / 65_536;
    let quotient6 = quotient5 / 65_536;
    let quotient7 = quotient6 / 65_536;
    ipaddr_hex4_characters((quotient7 % 65_536) as nat)
        + seq![':']
        + ipaddr_hex4_characters((quotient6 % 65_536) as nat)
        + seq![':']
        + ipaddr_hex4_characters((quotient5 % 65_536) as nat)
        + seq![':']
        + ipaddr_hex4_characters((quotient4 % 65_536) as nat)
        + seq![':']
        + ipaddr_hex4_characters((quotient3 % 65_536) as nat)
        + seq![':']
        + ipaddr_hex4_characters((quotient2 % 65_536) as nat)
        + seq![':']
        + ipaddr_hex4_characters((quotient1 % 65_536) as nat)
        + seq![':']
        + ipaddr_hex4_characters((address % 65_536) as nat)
}

pub open spec fn ipv6_join_groups(groups: Seq<Seq<char>>) -> Seq<char>
    decreases groups.len(),
{
    if groups.len() == 0 {
        Seq::<char>::empty()
    } else if groups.len() == 1 {
        groups[0]
    } else {
        groups[0] + seq![':']
            + ipv6_join_groups(groups.subrange(1, groups.len() as int))
    }
}

pub proof fn ipv6_rep_matches_joined_groups(
    groups: Seq<Seq<char>>,
    count: int,
)
    requires
        1 <= groups.len(),
        0 <= count,
        count + groups.len() == 8,
        forall|index: int| 0 <= index < groups.len() ==>
            #[trigger] ipv6_spec::ipv6_is_wf_H16(groups[index]),
    ensures
        ipv6_spec::ipv6_rep_0_matches(ipv6_join_groups(groups), count),
    decreases groups.len(),
{
    let first = groups[0];
    if groups.len() == 1 {
        assert(count == 7);
        assert(ipv6_join_groups(groups) == first) by {
            reveal(ipv6_join_groups);
        }
        reveal(ipv6_spec::ipv6_rep_0_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_join_groups(groups).len()
                && ipv6_spec::ipv6_is_wf_H16(
                    ipv6_join_groups(groups).subrange(0, split),
                )
                && 8 <= count + 1
                && count + 1 <= 8
                && split == ipv6_join_groups(groups).len()) by {
            let split = first.len() as int;
            assert(ipv6_join_groups(groups).subrange(0, split) == first) by {
                assert_seqs_equal!(
                    ipv6_join_groups(groups).subrange(0, split) == first
                );
            }
        }
    } else {
        let tail = groups.subrange(1, groups.len() as int);
        assert(1 <= tail.len());
        assert(count + 1 + tail.len() == 8);
        assert forall|index: int| 0 <= index < tail.len() implies
            #[trigger] ipv6_spec::ipv6_is_wf_H16(tail[index]) by {
            assert(tail[index] == groups[index + 1]);
        }
        ipv6_rep_matches_joined_groups(tail, count + 1);
        let joined_tail = ipv6_join_groups(tail);
        assert(
            ipv6_join_groups(groups) == first + seq![':'] + joined_tail
        ) by {
            reveal(ipv6_join_groups);
        }
        reveal(ipv6_spec::ipv6_rep_0_matches);
        assert(exists|split: int|
            0 <= split
                && split <= ipv6_join_groups(groups).len()
                && ipv6_spec::ipv6_is_wf_H16(
                    ipv6_join_groups(groups).subrange(0, split),
                )
                && count + 1 < 8
                && split + 1 <= ipv6_join_groups(groups).len()
                && ipv6_join_groups(groups).subrange(split, split + 1)
                    == seq![':']
                && ipv6_spec::ipv6_rep_0_matches(
                    ipv6_join_groups(groups).subrange(
                        split + 1,
                        ipv6_join_groups(groups).len() as int,
                    ),
                    count + 1,
                )) by {
            let split = first.len() as int;
            assert(
                ipv6_join_groups(groups).subrange(0, split) == first
            ) by {
                assert_seqs_equal!(
                    ipv6_join_groups(groups).subrange(0, split) == first
                );
            }
            assert(
                ipv6_join_groups(groups).subrange(split, split + 1)
                    == seq![':']
            ) by {
                assert_seqs_equal!(
                    ipv6_join_groups(groups).subrange(split, split + 1)
                        == seq![':']
                );
            }
            assert(
                ipv6_join_groups(groups).subrange(
                    split + 1,
                    ipv6_join_groups(groups).len() as int,
                ) == joined_tail
            ) by {
                assert_seqs_equal!(
                    ipv6_join_groups(groups).subrange(
                        split + 1,
                        ipv6_join_groups(groups).len() as int,
                    ) == joined_tail
                );
            }
        }
    }
}

pub open spec fn ipv6_canonical_characters(value: int) -> Seq<char>
    recommends
        0 <= value < ipv6_address_space() * 129,
{
    let address = value / 129;
    let prefix = value % 129;
    ipv6_full_characters(address)
        + seq!['/']
        + ipaddr_decimal_characters(prefix as nat)
}

pub proof fn ipv4_has_result_bounds(value: int)
    requires
        ipv4_has_result(value),
    ensures
        0 <= value < ipv4_address_space() * 33,
{
    reveal(ipv4_has_result);
    let input = choose|input: Seq<char>| ipv4_matches_result(input, value);
    reveal(ipv4_matches_result);
    let view = choose|view: ipv4_spec::IPv4View|
        ipv4_spec::ipv4_matches_view(input, view)
            && ipv4_spec::ipv4_view_valid(view)
            && ipv4_spec::ipv4_view_denotation(view) == value;
    reveal(ipv4_spec::ipv4_view_valid);
    reveal(ipv4_spec::ipv4_view_constraints);
    reveal(ipv4_spec::ipv4_constraints);
    reveal(ipv4_spec::ipv4_view_denotation);
    reveal(ipv4_address_space);
    reveal_with_fuel(ipv4_spec::triptych_int_pow, 33);
}

pub open spec fn ipaddr_pow_65536(exponent: int) -> int
    decreases if exponent > 0 { exponent } else { 0 },
{
    if exponent > 0 {
        65_536 * ipaddr_pow_65536(exponent - 1)
    } else {
        1
    }
}

pub proof fn ipv6_triptych_pow_add(base: int, left: int, right: int)
    requires
        0 <= left,
        0 <= right,
    ensures
        ipv6_spec::triptych_int_pow(base, left + right)
            == ipv6_spec::triptych_int_pow(base, left)
                * ipv6_spec::triptych_int_pow(base, right),
    decreases left,
{
    if left == 0 {
        reveal(ipv6_spec::triptych_int_pow);
    } else {
        ipv6_triptych_pow_add(base, left - 1, right);
        lemma_mul_is_associative(
            base,
            ipv6_spec::triptych_int_pow(base, left - 1),
            ipv6_spec::triptych_int_pow(base, right),
        );
        reveal(ipv6_spec::triptych_int_pow);
    }
}

pub proof fn ipv6_pow_sixteen_chunks(chunks: int)
    requires
        0 <= chunks,
    ensures
        ipv6_spec::triptych_int_pow(2, 16 * chunks)
            == ipaddr_pow_65536(chunks),
    decreases chunks,
{
    assert(ipv6_spec::triptych_int_pow(2, 16) == 65_536) by {
        reveal_with_fuel(ipv6_spec::triptych_int_pow, 17);
    }
    if chunks == 0 {
        reveal(ipaddr_pow_65536);
        reveal(ipv6_spec::triptych_int_pow);
    } else {
        ipv6_pow_sixteen_chunks(chunks - 1);
        ipv6_triptych_pow_add(2, 16 * (chunks - 1), 16);
        reveal(ipaddr_pow_65536);
    }
}

pub proof fn ipv6_generated_address_space()
    ensures
        ipv6_spec::triptych_int_pow(2, 128) == ipv6_address_space(),
{
    ipv6_pow_sixteen_chunks(8);
    reveal(ipv6_address_space);
    reveal_with_fuel(ipaddr_pow_65536, 9);
}

pub proof fn ipv6_has_result_bounds(value: int)
    requires
        ipv6_has_result(value),
    ensures
        0 <= value < ipv6_address_space() * 129,
{
    reveal(ipv6_has_result);
    let input = choose|input: Seq<char>| ipv6_matches_result(input, value);
    reveal(ipv6_matches_result);
    let view = choose|view: ipv6_spec::IPv6View|
        ipv6_spec::ipv6_matches_view(input, view)
            && ipv6_spec::ipv6_view_valid(view)
            && ipv6_spec::ipv6_view_denotation(view) == value;
    reveal(ipv6_spec::ipv6_view_valid);
    reveal(ipv6_spec::ipv6_view_constraints);
    reveal(ipv6_spec::ipv6_constraints);
    reveal(ipv6_spec::ipv6_view_denotation);
    ipv6_generated_address_space();
}

#[verifier::spinoff_prover]
pub proof fn ipv6_full_characters_value(address: int)
    requires
        0 <= address < ipv6_address_space(),
    ensures
        ipv6_spec::triptych_hex_seq_of(ipv6_full_characters(address))
            == address,
{
    reveal(ipv6_address_space);
    let quotient1 = address / 65_536;
    let quotient2 = quotient1 / 65_536;
    let quotient3 = quotient2 / 65_536;
    let quotient4 = quotient3 / 65_536;
    let quotient5 = quotient4 / 65_536;
    let quotient6 = quotient5 / 65_536;
    let quotient7 = quotient6 / 65_536;
    let quotient8 = quotient7 / 65_536;
    lemma_mod_pos_bound(address, 65_536);
    lemma_mod_pos_bound(quotient1, 65_536);
    lemma_mod_pos_bound(quotient2, 65_536);
    lemma_mod_pos_bound(quotient3, 65_536);
    lemma_mod_pos_bound(quotient4, 65_536);
    lemma_mod_pos_bound(quotient5, 65_536);
    lemma_mod_pos_bound(quotient6, 65_536);
    lemma_mod_pos_bound(quotient7, 65_536);
    lemma_fundamental_div_mod(address, 65_536);
    lemma_fundamental_div_mod(quotient1, 65_536);
    lemma_fundamental_div_mod(quotient2, 65_536);
    lemma_fundamental_div_mod(quotient3, 65_536);
    lemma_fundamental_div_mod(quotient4, 65_536);
    lemma_fundamental_div_mod(quotient5, 65_536);
    lemma_fundamental_div_mod(quotient6, 65_536);
    lemma_fundamental_div_mod(quotient7, 65_536);
    assert(quotient8 == 0);

    let segment0 = quotient7 % 65_536;
    let segment1 = quotient6 % 65_536;
    let segment2 = quotient5 % 65_536;
    let segment3 = quotient4 % 65_536;
    let segment4 = quotient3 % 65_536;
    let segment5 = quotient2 % 65_536;
    let segment6 = quotient1 % 65_536;
    let segment7 = address % 65_536;
    let group0 = ipaddr_hex4_characters(segment0 as nat);
    let group1 = ipaddr_hex4_characters(segment1 as nat);
    let group2 = ipaddr_hex4_characters(segment2 as nat);
    let group3 = ipaddr_hex4_characters(segment3 as nat);
    let group4 = ipaddr_hex4_characters(segment4 as nat);
    let group5 = ipaddr_hex4_characters(segment5 as nat);
    let group6 = ipaddr_hex4_characters(segment6 as nat);
    let group7 = ipaddr_hex4_characters(segment7 as nat);
    let prefix0 = group0;
    let prefix1 = prefix0 + seq![':'] + group1;
    let prefix2 = prefix1 + seq![':'] + group2;
    let prefix3 = prefix2 + seq![':'] + group3;
    let prefix4 = prefix3 + seq![':'] + group4;
    let prefix5 = prefix4 + seq![':'] + group5;
    let prefix6 = prefix5 + seq![':'] + group6;
    let prefix7 = prefix6 + seq![':'] + group7;

    ipv6_hex4_characters_value(segment0 as nat);
    ipv6_hex_seq_append_group(prefix0, 0, 0, 0, segment1 as nat);
    ipv6_hex_seq_append_group(prefix1, 0, 0, 0, segment2 as nat);
    ipv6_hex_seq_append_group(prefix2, 0, 0, 0, segment3 as nat);
    ipv6_hex_seq_append_group(prefix3, 0, 0, 0, segment4 as nat);
    ipv6_hex_seq_append_group(prefix4, 0, 0, 0, segment5 as nat);
    ipv6_hex_seq_append_group(prefix5, 0, 0, 0, segment6 as nat);
    ipv6_hex_seq_append_group(prefix6, 0, 0, 0, segment7 as nat);
    assert(ipv6_full_characters(address) == prefix7) by {
        reveal(ipv6_full_characters);
    }
    reveal(ipv6_spec::triptych_hex_seq_of);
}

pub proof fn ipv6_full_characters_wf(address: int)
    requires
        0 <= address < ipv6_address_space(),
    ensures
        ipv6_spec::ipv6_is_wf_Full(ipv6_full_characters(address)),
        ipv6_spec::ipv6_matches_Full(
            ipv6_full_characters(address),
            ipv6_spec::IPv6View {
                input: ipv6_full_characters(address),
                full: ipv6_full_characters(address),
                left: seq![],
                right: seq![],
                prefix: seq![],
            },
        ),
{
    let quotient1 = address / 65_536;
    let quotient2 = quotient1 / 65_536;
    let quotient3 = quotient2 / 65_536;
    let quotient4 = quotient3 / 65_536;
    let quotient5 = quotient4 / 65_536;
    let quotient6 = quotient5 / 65_536;
    let quotient7 = quotient6 / 65_536;
    lemma_mod_pos_bound(address, 65_536);
    lemma_mod_pos_bound(quotient1, 65_536);
    lemma_mod_pos_bound(quotient2, 65_536);
    lemma_mod_pos_bound(quotient3, 65_536);
    lemma_mod_pos_bound(quotient4, 65_536);
    lemma_mod_pos_bound(quotient5, 65_536);
    lemma_mod_pos_bound(quotient6, 65_536);
    lemma_mod_pos_bound(quotient7, 65_536);
    let group0 = ipaddr_hex4_characters((quotient7 % 65_536) as nat);
    let group1 = ipaddr_hex4_characters((quotient6 % 65_536) as nat);
    let group2 = ipaddr_hex4_characters((quotient5 % 65_536) as nat);
    let group3 = ipaddr_hex4_characters((quotient4 % 65_536) as nat);
    let group4 = ipaddr_hex4_characters((quotient3 % 65_536) as nat);
    let group5 = ipaddr_hex4_characters((quotient2 % 65_536) as nat);
    let group6 = ipaddr_hex4_characters((quotient1 % 65_536) as nat);
    let group7 = ipaddr_hex4_characters((address % 65_536) as nat);
    ipv6_hex4_characters_wf((quotient7 % 65_536) as nat);
    ipv6_hex4_characters_wf((quotient6 % 65_536) as nat);
    ipv6_hex4_characters_wf((quotient5 % 65_536) as nat);
    ipv6_hex4_characters_wf((quotient4 % 65_536) as nat);
    ipv6_hex4_characters_wf((quotient3 % 65_536) as nat);
    ipv6_hex4_characters_wf((quotient2 % 65_536) as nat);
    ipv6_hex4_characters_wf((quotient1 % 65_536) as nat);
    ipv6_hex4_characters_wf((address % 65_536) as nat);
    assert(ipv6_spec::ipv6_is_wf_H16(group0)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    assert(ipv6_spec::ipv6_is_wf_H16(group1)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    assert(ipv6_spec::ipv6_is_wf_H16(group2)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    assert(ipv6_spec::ipv6_is_wf_H16(group3)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    assert(ipv6_spec::ipv6_is_wf_H16(group4)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    assert(ipv6_spec::ipv6_is_wf_H16(group5)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    assert(ipv6_spec::ipv6_is_wf_H16(group6)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    assert(ipv6_spec::ipv6_is_wf_H16(group7)) by {
        reveal(ipv6_spec::ipv6_is_wf_H16);
    }
    let groups = seq![
        group0, group1, group2, group3, group4, group5, group6, group7
    ];
    assert forall|index: int| 0 <= index < groups.len() implies
        #[trigger] ipv6_spec::ipv6_is_wf_H16(groups[index]) by {
        if index == 0 {
        } else if index == 1 {
        } else if index == 2 {
        } else if index == 3 {
        } else if index == 4 {
        } else if index == 5 {
        } else if index == 6 {
        } else {
            assert(index == 7);
        }
    }
    ipv6_rep_matches_joined_groups(groups, 0);
    assert(
        ipv6_join_groups(groups) == ipv6_full_characters(address)
    ) by {
        reveal_with_fuel(ipv6_join_groups, 9);
        reveal(ipv6_full_characters);
    }
    reveal(ipv6_spec::ipv6_is_wf_Full);
    reveal(ipv6_spec::ipv6_matches_Full);
}

#[verifier::rlimit(250)]
pub proof fn ipv6_canonical_matches_result(value: int)
    requires
        ipv6_has_result(value),
    ensures
        ipv6_matches_result(ipv6_canonical_characters(value), value),
        ipv6_spec::ipv6_is_valid(ipv6_canonical_characters(value)),
{
    ipv6_has_result_bounds(value);
    let address = value / 129;
    let prefix = value % 129;
    lemma_mod_pos_bound(value, 129);
    lemma_fundamental_div_mod(value, 129);
    assert(0 <= address < ipv6_address_space());
    assert(0 <= prefix <= 128);
    let full = ipv6_full_characters(address);
    let prefix_characters = ipaddr_decimal_characters(prefix as nat);
    let input = full + seq!['/'] + prefix_characters;
    let view = ipv6_spec::IPv6View {
        input,
        full,
        left: seq![],
        right: seq![],
        prefix: prefix_characters,
    };
    ipv6_full_characters_value(address);
    ipv6_full_characters_wf(address);
    ipv6_decimal_characters_properties(prefix as nat);
    assert(ipv6_canonical_characters(value) == input) by {
        reveal(ipv6_canonical_characters);
    }
    assert(ipv6_spec::ipv6_matches_Full(full, view)) by {
        reveal(ipv6_spec::ipv6_matches_Full);
        reveal(ipv6_spec::ipv6_is_wf_Full);
    }
    assert(ipv6_spec::ipv6_matches_view(input, view)) by {
        reveal(ipv6_spec::ipv6_matches_view);
        reveal(ipv6_spec::ipv6_matches_V6Net);
        reveal(ipv6_spec::ipv6_matches_V6Addr);
        reveal(ipv6_spec::ipv6_matches_Prefix);
    }
    assert(ipv6_spec::ipv6_view_denotation(view) == value) by {
        reveal(ipv6_spec::ipv6_view_denotation);
        reveal(ipv6_spec::ipv6_value);
        assert(full.len() == 39) by {
            reveal(ipv6_full_characters);
        }
        assert(full != seq![]);
        assert(ipv6_spec::triptych_hex_seq_of(full) == address);
        assert(ipv6_spec::triptych_nat_of(prefix_characters) == prefix);
    }
    assert(ipv6_spec::ipv6_view_valid(view)) by {
        reveal(ipv6_spec::ipv6_view_valid);
        reveal(ipv6_spec::ipv6_view_wf_constraints);
        reveal(ipv6_spec::ipv6_wf_constraints);
        reveal(ipv6_spec::triptych_segments_of);
        reveal(ipv6_spec::ipv6_view_constraints);
        reveal(ipv6_spec::ipv6_constraints);
        assert(ipv6_spec::ipv6_value(
            full,
            seq![],
            seq![],
            prefix_characters,
        ) == value);
        ipv6_generated_address_space();
    }
    assert(ipv6_matches_result(input, value)) by {
        reveal(ipv6_matches_result);
    }
    assert(ipv6_spec::ipv6_is_wf_V6Net(input)) by {
        reveal(ipv6_spec::ipv6_is_wf_V6Net);
        reveal(ipv6_spec::ipv6_is_wf_V6Addr);
        reveal(ipv6_spec::ipv6_is_wf_Prefix);
    }
    assert(ipv6_spec::ipv6_satisfies_wf_constraints(input)) by {
        reveal(ipv6_spec::ipv6_satisfies_wf_constraints);
    }
    assert(ipv6_spec::ipv6_is_wf(input)) by {
        reveal(ipv6_spec::ipv6_is_wf);
    }
    assert(ipv6_spec::ipv6_satisfies_constraints(input)) by {
        reveal(ipv6_spec::ipv6_satisfies_constraints);
    }
    assert(ipv6_spec::ipv6_is_valid(input)) by {
        reveal(ipv6_spec::ipv6_is_valid);
    }
}

pub proof fn ipv4_canonical_matches_result(value: int)
    requires
        ipv4_has_result(value),
    ensures
        ipv4_matches_result(ipv4_canonical_characters(value), value),
        ipv4_spec::ipv4_is_valid(ipv4_canonical_characters(value)),
{
    ipv4_has_result_bounds(value);
    reveal(ipv4_address_space);
    let address = value / 33;
    let prefix = value % 33;
    lemma_mod_pos_bound(value, 33);
    lemma_fundamental_div_mod(value, 33);
    assert(0 <= address < 4_294_967_296);
    assert(0 <= prefix <= 32);

    let quotient1 = address / 256;
    let quotient2 = quotient1 / 256;
    let quotient3 = quotient2 / 256;
    let quotient4 = quotient3 / 256;
    lemma_mod_pos_bound(address, 256);
    lemma_mod_pos_bound(quotient1, 256);
    lemma_mod_pos_bound(quotient2, 256);
    lemma_mod_pos_bound(quotient3, 256);
    lemma_fundamental_div_mod(address, 256);
    lemma_fundamental_div_mod(quotient1, 256);
    lemma_fundamental_div_mod(quotient2, 256);
    lemma_fundamental_div_mod(quotient3, 256);
    assert(0 <= quotient1);
    assert(0 <= quotient2);
    assert(0 <= quotient3);
    assert(quotient4 == 0);

    let oct1_value = quotient3 % 256;
    let oct2_value = quotient2 % 256;
    let oct3_value = quotient1 % 256;
    let oct4_value = address % 256;
    let oct1 = ipaddr_decimal_characters(oct1_value as nat);
    let oct2 = ipaddr_decimal_characters(oct2_value as nat);
    let oct3 = ipaddr_decimal_characters(oct3_value as nat);
    let oct4 = ipaddr_decimal_characters(oct4_value as nat);
    let prefix_characters = ipaddr_decimal_characters(prefix as nat);
    let address_characters =
        oct1 + seq!['.'] + oct2 + seq!['.'] + oct3 + seq!['.'] + oct4;
    let input = address_characters + seq!['/'] + prefix_characters;
    let view = ipv4_spec::IPv4View {
        input,
        oct1,
        oct2,
        oct3,
        oct4,
        prefix: prefix_characters,
    };

    ipv4_decimal_characters_properties(oct1_value as nat);
    ipv4_decimal_characters_properties(oct2_value as nat);
    ipv4_decimal_characters_properties(oct3_value as nat);
    ipv4_decimal_characters_properties(oct4_value as nat);
    ipv4_decimal_characters_properties(prefix as nat);
    assert(prefix_characters.len() <= 2) by {
        if prefix < 10 {
            reveal(ipaddr_decimal_characters);
        } else {
            assert(prefix < 100);
            reveal(ipaddr_decimal_characters);
        }
    }

    assert(ipv4_canonical_characters(value) == input) by {
        reveal(ipv4_canonical_characters);
    }
    assert(ipv4_spec::ipv4_matches_view(input, view)) by {
        reveal(ipv4_spec::ipv4_matches_view);
        reveal(ipv4_spec::ipv4_matches_V4Net);
        reveal(ipv4_spec::ipv4_matches_V4Addr);
        reveal(ipv4_spec::ipv4_matches_Oct1);
        reveal(ipv4_spec::ipv4_matches_Oct2);
        reveal(ipv4_spec::ipv4_matches_Oct3);
        reveal(ipv4_spec::ipv4_matches_Oct4);
        reveal(ipv4_spec::ipv4_matches_Prefix);
    }
    assert(ipv4_spec::ipv4_view_denotation(view) == value) by {
        reveal(ipv4_spec::ipv4_view_denotation);
        reveal(ipv4_spec::ipv4_value);
        assert(ipv4_spec::triptych_nat_of(oct1) == oct1_value);
        assert(ipv4_spec::triptych_nat_of(oct2) == oct2_value);
        assert(ipv4_spec::triptych_nat_of(oct3) == oct3_value);
        assert(ipv4_spec::triptych_nat_of(oct4) == oct4_value);
        assert(ipv4_spec::triptych_nat_of(prefix_characters) == prefix);
    }
    assert(ipv4_spec::ipv4_view_valid(view)) by {
        reveal(ipv4_spec::ipv4_view_valid);
        reveal(ipv4_spec::ipv4_view_wf_constraints);
        reveal(ipv4_spec::ipv4_wf_constraints);
        reveal(ipv4_spec::ipv4_view_constraints);
        reveal(ipv4_spec::ipv4_constraints);
        assert(ipv4_spec::ipv4_value(oct1, oct2, oct3, oct4, prefix_characters)
            == value);
        reveal_with_fuel(ipv4_spec::triptych_int_pow, 33);
    }
    assert(ipv4_matches_result(input, value)) by {
        reveal(ipv4_matches_result);
    }

    assert(ipv4_spec::ipv4_is_wf_V4Net(input)) by {
        reveal(ipv4_spec::ipv4_is_wf_V4Net);
        reveal(ipv4_spec::ipv4_is_wf_V4Addr);
        reveal(ipv4_spec::ipv4_is_wf_Oct1);
        reveal(ipv4_spec::ipv4_is_wf_Oct2);
        reveal(ipv4_spec::ipv4_is_wf_Oct3);
        reveal(ipv4_spec::ipv4_is_wf_Oct4);
        reveal(ipv4_spec::ipv4_is_wf_Prefix);
    }
    assert(ipv4_spec::ipv4_satisfies_wf_constraints(input)) by {
        reveal(ipv4_spec::ipv4_satisfies_wf_constraints);
    }
    assert(ipv4_spec::ipv4_is_wf(input)) by {
        reveal(ipv4_spec::ipv4_is_wf);
    }
    assert(ipv4_spec::ipv4_satisfies_constraints(input)) by {
        reveal(ipv4_spec::ipv4_satisfies_constraints);
    }
    assert(ipv4_spec::ipv4_is_valid(input)) by {
        reveal(ipv4_spec::ipv4_is_valid);
    }
}

pub struct IpAddrPrinter {}

impl IpAddrPrinter {
    /** Canonical IPv4 rendering accepted by Cedar's production parser. */
    pub fn ipv4_to_string(address: u32, prefix: u8) -> (result: String)
        requires
            prefix <= 32,
        ensures
            result@ == ipv4_canonical_characters(
                address as int * 33 + prefix as int,
            ),
    {
        let quotient1 = address / 256;
        let quotient2 = quotient1 / 256;
        let quotient3 = quotient2 / 256;
        let octet1 = (quotient3 % 256) as u16;
        let octet2 = (quotient2 % 256) as u16;
        let octet3 = (quotient1 % 256) as u16;
        let octet4 = (address % 256) as u16;
        proof {
            lemma_mod_pos_bound(quotient3 as int, 256);
            lemma_mod_pos_bound(quotient2 as int, 256);
            lemma_mod_pos_bound(quotient1 as int, 256);
            lemma_mod_pos_bound(address as int, 256);
        }
        let mut result = String::new();
        ipaddr_push_decimal(&mut result, octet1);
        result.push('.');
        ipaddr_push_decimal(&mut result, octet2);
        result.push('.');
        ipaddr_push_decimal(&mut result, octet3);
        result.push('.');
        ipaddr_push_decimal(&mut result, octet4);
        result.push('/');
        ipaddr_push_decimal(&mut result, prefix as u16);
        proof {
            let packed = address as int * 33 + prefix as int;
            lemma_fundamental_div_mod_converse(
                packed,
                33,
                address as int,
                prefix as int,
            );
            reveal(ipv4_canonical_characters);
        }
        result
    }

    /**
     * Canonical IPv6 rendering as eight fixed-width lowercase hextets.
     *
     * This is accepted by Cedar for every IPv6 value, including IPv4-mapped
     * addresses that `std::net::Ipv6Addr::Display` renders in a non-roundtripping
     * mixed dotted form.
     */
    pub fn ipv6_to_string(address: u128, prefix: u8) -> (result: String)
        requires
            prefix <= 128,
        ensures
            result@ == ipv6_canonical_characters(
                address as int * 129 + prefix as int,
            ),
    {
        let quotient1 = address / 65_536;
        let quotient2 = quotient1 / 65_536;
        let quotient3 = quotient2 / 65_536;
        let quotient4 = quotient3 / 65_536;
        let quotient5 = quotient4 / 65_536;
        let quotient6 = quotient5 / 65_536;
        let quotient7 = quotient6 / 65_536;
        let mut result = String::new();
        ipaddr_push_hex4(&mut result, (quotient7 % 65_536) as u16);
        result.push(':');
        ipaddr_push_hex4(&mut result, (quotient6 % 65_536) as u16);
        result.push(':');
        ipaddr_push_hex4(&mut result, (quotient5 % 65_536) as u16);
        result.push(':');
        ipaddr_push_hex4(&mut result, (quotient4 % 65_536) as u16);
        result.push(':');
        ipaddr_push_hex4(&mut result, (quotient3 % 65_536) as u16);
        result.push(':');
        ipaddr_push_hex4(&mut result, (quotient2 % 65_536) as u16);
        result.push(':');
        ipaddr_push_hex4(&mut result, (quotient1 % 65_536) as u16);
        result.push(':');
        ipaddr_push_hex4(&mut result, (address % 65_536) as u16);
        result.push('/');
        ipaddr_push_decimal(&mut result, prefix as u16);
        proof {
            let packed = address as int * 129 + prefix as int;
            lemma_fundamental_div_mod_converse(
                packed,
                129,
                address as int,
                prefix as int,
            );
            reveal(ipv6_canonical_characters);
            reveal(ipv6_full_characters);
        }
        result
    }
}

} // verus!
