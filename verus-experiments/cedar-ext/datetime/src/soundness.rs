// Implementation of Triptych's generated external-parser contract.

#[cfg(verus_only)]
use vstd::assert_seqs_equal;
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::contract::datetime_matches_result;
use crate::contract::DatetimeExternalParserContract;
#[cfg(verus_only)]
use crate::model::{
    datetime_days_from_civil, datetime_days_in_month, datetime_digit, datetime_epoch_millis,
    datetime_external_parse_spec, datetime_four_digits, datetime_is_leap_year, datetime_parse_spec,
    datetime_three_digits, datetime_two_digits, datetime_valid_date,
};
use crate::optimized::DatetimeParser;
#[cfg(verus_only)]
use crate::spec::*;

verus! {

pub proof fn datetime_two_digit_capture_value(digits: Seq<char>)
    requires
        digits.len() == 2,
        forall|index: int| 0 <= index < digits.len() ==>
            #[trigger] triptych_is_digit(digits[index]),
    ensures
        datetime_two_digits(digits, 0) == Some(triptych_nat_of(digits)),
{
    assert(triptych_is_digit(digits[0]));
    assert(triptych_is_digit(digits[1]));
    reveal(triptych_is_digit);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
    reveal(triptych_nat_of);
    reveal_with_fuel(triptych_nat_of_from, 3);
}

pub proof fn datetime_three_digit_capture_value(digits: Seq<char>)
    requires
        digits.len() == 3,
        forall|index: int| 0 <= index < digits.len() ==>
            #[trigger] triptych_is_digit(digits[index]),
    ensures
        datetime_three_digits(digits, 0) == Some(triptych_nat_of(digits)),
{
    assert(triptych_is_digit(digits[0]));
    assert(triptych_is_digit(digits[1]));
    assert(triptych_is_digit(digits[2]));
    reveal(triptych_is_digit);
    reveal(datetime_three_digits);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
    reveal(triptych_nat_of);
    reveal_with_fuel(triptych_nat_of_from, 4);
}

pub proof fn datetime_four_digit_capture_value(digits: Seq<char>)
    requires
        digits.len() == 4,
        forall|index: int| 0 <= index < digits.len() ==>
            #[trigger] triptych_is_digit(digits[index]),
    ensures
        datetime_four_digits(digits, 0) == Some(triptych_nat_of(digits)),
{
    assert(triptych_is_digit(digits[0]));
    assert(triptych_is_digit(digits[1]));
    assert(triptych_is_digit(digits[2]));
    assert(triptych_is_digit(digits[3]));
    reveal(triptych_is_digit);
    reveal(datetime_four_digits);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
    reveal(triptych_nat_of);
    reveal_with_fuel(triptych_nat_of_from, 5);
}

pub proof fn datetime_two_digit_subrange_facts(
    input: Seq<char>,
    index: int,
    value: int,
)
    requires
        0 <= index,
        index + 2 <= input.len(),
        datetime_two_digits(input, index) == Some(value),
    ensures
        input.subrange(index, index + 2).len() == 2,
        forall|offset: int| 0 <= offset < 2 ==>
            #[trigger] triptych_is_digit(input.subrange(index, index + 2)[offset]),
        triptych_nat_of(input.subrange(index, index + 2)) == value,
        0 <= value <= 99,
{
    let digits = input.subrange(index, index + 2);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
    assert(digits[0] == input[index]);
    assert(digits[1] == input[index + 1]);
    assert forall|offset: int| 0 <= offset < 2 implies
        #[trigger] triptych_is_digit(digits[offset]) by {
        if offset == 0 {
            reveal(triptych_is_digit);
        } else {
            assert(offset == 1);
            reveal(triptych_is_digit);
        }
    }
    datetime_two_digit_capture_value(digits);
}

pub proof fn datetime_three_digit_subrange_facts(
    input: Seq<char>,
    index: int,
    value: int,
)
    requires
        0 <= index,
        index + 3 <= input.len(),
        datetime_three_digits(input, index) == Some(value),
    ensures
        input.subrange(index, index + 3).len() == 3,
        forall|offset: int| 0 <= offset < 3 ==>
            #[trigger] triptych_is_digit(input.subrange(index, index + 3)[offset]),
        triptych_nat_of(input.subrange(index, index + 3)) == value,
{
    let digits = input.subrange(index, index + 3);
    reveal(datetime_three_digits);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
    assert(digits[0] == input[index]);
    assert(digits[1] == input[index + 1]);
    assert(digits[2] == input[index + 2]);
    assert forall|offset: int| 0 <= offset < 3 implies
        #[trigger] triptych_is_digit(digits[offset]) by {
        if offset == 0 {
            reveal(triptych_is_digit);
        } else if offset == 1 {
            reveal(triptych_is_digit);
        } else {
            assert(offset == 2);
            reveal(triptych_is_digit);
        }
    }
    datetime_three_digit_capture_value(digits);
}

pub proof fn datetime_four_digit_subrange_facts(
    input: Seq<char>,
    index: int,
    value: int,
)
    requires
        0 <= index,
        index + 4 <= input.len(),
        datetime_four_digits(input, index) == Some(value),
    ensures
        input.subrange(index, index + 4).len() == 4,
        forall|offset: int| 0 <= offset < 4 ==>
            #[trigger] triptych_is_digit(input.subrange(index, index + 4)[offset]),
        triptych_nat_of(input.subrange(index, index + 4)) == value,
{
    let digits = input.subrange(index, index + 4);
    reveal(datetime_four_digits);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
    assert(digits[0] == input[index]);
    assert(digits[1] == input[index + 1]);
    assert(digits[2] == input[index + 2]);
    assert(digits[3] == input[index + 3]);
    assert forall|offset: int| 0 <= offset < 4 implies
        #[trigger] triptych_is_digit(digits[offset]) by {
        if offset == 0 {
            reveal(triptych_is_digit);
        } else if offset == 1 {
            reveal(triptych_is_digit);
        } else if offset == 2 {
            reveal(triptych_is_digit);
        } else {
            assert(offset == 3);
            reveal(triptych_is_digit);
        }
    }
    datetime_four_digit_capture_value(digits);
}

pub proof fn datetime_date_subranges_match(
    input: Seq<char>,
    view: DatetimeView,
    year: int,
    month: int,
    day: int,
)
    requires
        10 <= input.len(),
        input[4] == '-',
        input[7] == '-',
        datetime_four_digits(input, 0) == Some(year),
        datetime_two_digits(input, 5) == Some(month),
        datetime_two_digits(input, 8) == Some(day),
        view.yyyy == input.subrange(0, 4),
        view.mm == input.subrange(5, 7),
        view.dd == input.subrange(8, 10),
    ensures
        datetime_matches_Date(input.subrange(0, 10), view),
        datetime_is_wf_Date(input.subrange(0, 10)),
        triptych_nat_of(view.yyyy) == year,
        triptych_nat_of(view.mm) == month,
        triptych_nat_of(view.dd) == day,
{
    let date = input.subrange(0, 10);
    let yyyy = input.subrange(0, 4);
    let mm = input.subrange(5, 7);
    let dd = input.subrange(8, 10);
    datetime_four_digit_subrange_facts(input, 0, year);
    datetime_two_digit_subrange_facts(input, 5, month);
    datetime_two_digit_subrange_facts(input, 8, day);
    assert(datetime_matches_YYYY(yyyy, view)) by {
        reveal(datetime_matches_YYYY);
    }
    assert(datetime_matches_MM(mm, view)) by {
        reveal(datetime_matches_MM);
    }
    assert(datetime_matches_DD(dd, view)) by {
        reveal(datetime_matches_DD);
    }
    assert(date == yyyy + seq!['-'] + mm + seq!['-'] + dd) by {
        assert_seqs_equal!(date == yyyy + seq!['-'] + mm + seq!['-'] + dd);
    }
    assert(datetime_matches_Date(date, view)) by {
        reveal(datetime_matches_Date);
    }
    assert(datetime_is_wf_YYYY(yyyy)) by {
        reveal(datetime_is_wf_YYYY);
    }
    assert(datetime_is_wf_MM(mm)) by {
        reveal(datetime_is_wf_MM);
    }
    assert(datetime_is_wf_DD(dd)) by {
        reveal(datetime_is_wf_DD);
    }
    reveal(datetime_is_wf_Date);
}

pub proof fn datetime_time_subranges_match(
    input: Seq<char>,
    view: DatetimeView,
    hour: int,
    minute: int,
    second: int,
)
    requires
        19 <= input.len(),
        input[13] == ':',
        input[16] == ':',
        datetime_two_digits(input, 11) == Some(hour),
        datetime_two_digits(input, 14) == Some(minute),
        datetime_two_digits(input, 17) == Some(second),
        view.time_hh == input.subrange(11, 13),
        view.time_mm == input.subrange(14, 16),
        view.ss == input.subrange(17, 19),
    ensures
        datetime_matches_Time(input.subrange(11, 19), view),
        datetime_is_wf_Time(input.subrange(11, 19)),
        triptych_nat_of(view.time_hh) == hour,
        triptych_nat_of(view.time_mm) == minute,
        triptych_nat_of(view.ss) == second,
{
    let time = input.subrange(11, 19);
    let hh = input.subrange(11, 13);
    let mm = input.subrange(14, 16);
    let ss = input.subrange(17, 19);
    datetime_two_digit_subrange_facts(input, 11, hour);
    datetime_two_digit_subrange_facts(input, 14, minute);
    datetime_two_digit_subrange_facts(input, 17, second);
    assert(datetime_matches_hh(hh, view)) by {
        reveal(datetime_matches_hh);
    }
    assert(datetime_matches_mm(mm, view)) by {
        reveal(datetime_matches_mm);
    }
    assert(datetime_matches_ss(ss, view)) by {
        reveal(datetime_matches_ss);
    }
    assert(time == hh + seq![':'] + mm + seq![':'] + ss) by {
        assert_seqs_equal!(time == hh + seq![':'] + mm + seq![':'] + ss);
    }
    assert(datetime_matches_Time(time, view)) by {
        reveal(datetime_matches_Time);
    }
    assert(datetime_is_wf_hh(hh)) by {
        reveal(datetime_is_wf_hh);
    }
    assert(datetime_is_wf_mm(mm)) by {
        reveal(datetime_is_wf_mm);
    }
    assert(datetime_is_wf_ss(ss)) by {
        reveal(datetime_is_wf_ss);
    }
    reveal(datetime_is_wf_Time);
}

pub proof fn datetime_sss_subrange_matches(
    input: Seq<char>,
    view: DatetimeView,
    millisecond: int,
)
    requires
        23 <= input.len(),
        datetime_three_digits(input, 20) == Some(millisecond),
        view.sss == input.subrange(20, 23),
    ensures
        datetime_matches_SSS(input.subrange(20, 23), view),
        datetime_is_wf_SSS(input.subrange(20, 23)),
        triptych_nat_of(view.sss) == millisecond,
{
    let sss = input.subrange(20, 23);
    datetime_three_digit_subrange_facts(input, 20, millisecond);
    assert(datetime_matches_SSS(sss, view)) by {
        reveal(datetime_matches_SSS);
    }
    reveal(datetime_is_wf_SSS);
}

pub proof fn datetime_offset_subranges_match(
    input: Seq<char>,
    view: DatetimeView,
    start: int,
    offset_hour: int,
    offset_minute: int,
)
    requires
        0 <= start,
        start + 5 <= input.len(),
        input[start] == '+' || input[start] == '-',
        datetime_two_digits(input, start + 1) == Some(offset_hour),
        datetime_two_digits(input, start + 3) == Some(offset_minute),
        view.offset == input.subrange(start, start + 5),
        view.offset_hh == input.subrange(start + 1, start + 3),
        view.offset_mm == input.subrange(start + 3, start + 5),
    ensures
        datetime_matches_Offset(input.subrange(start, start + 5), view),
        datetime_is_wf_Offset(input.subrange(start, start + 5)),
        triptych_nat_of(view.offset_hh) == offset_hour,
        triptych_nat_of(view.offset_mm) == offset_minute,
        triptych_sign_of(view.offset) == if input[start] == '+' { 1 } else { -1 },
{
    let offset = input.subrange(start, start + 5);
    let hh = input.subrange(start + 1, start + 3);
    let mm = input.subrange(start + 3, start + 5);
    datetime_two_digit_subrange_facts(input, start + 1, offset_hour);
    datetime_two_digit_subrange_facts(input, start + 3, offset_minute);
    assert(datetime_matches_hh(hh, view)) by {
        reveal(datetime_matches_hh);
    }
    assert(datetime_matches_mm(mm, view)) by {
        reveal(datetime_matches_mm);
    }
    if input[start] == '+' {
        assert(offset == seq!['+'] + hh + mm) by {
            assert_seqs_equal!(offset == seq!['+'] + hh + mm);
        }
    } else {
        assert(input[start] == '-');
        assert(offset == seq!['-'] + hh + mm) by {
            assert_seqs_equal!(offset == seq!['-'] + hh + mm);
        }
    }
    assert(datetime_matches_Offset(offset, view)) by {
        reveal(datetime_matches_Offset);
    }
    assert(datetime_is_wf_hh(hh)) by {
        reveal(datetime_is_wf_hh);
    }
    assert(datetime_is_wf_mm(mm)) by {
        reveal(datetime_is_wf_mm);
    }
    assert(datetime_is_wf_Offset(offset)) by {
        reveal(datetime_is_wf_Offset);
    }
    reveal(triptych_sign_of);
}

pub proof fn datetime_date_capture_facts(date: Seq<char>, view: DatetimeView)
    requires
        datetime_matches_Date(date, view),
    ensures
        date.len() == 10,
        date[4] == '-',
        date[7] == '-',
        datetime_four_digits(date, 0) == Some(triptych_nat_of(view.yyyy)),
        datetime_two_digits(date, 5) == Some(triptych_nat_of(view.mm)),
        datetime_two_digits(date, 8) == Some(triptych_nat_of(view.dd)),
{
    reveal(datetime_matches_Date);
    let yyyy = choose|yyyy: Seq<char>|
        exists|mm: Seq<char>, dd: Seq<char>|
            date == yyyy + seq!['-'] + mm + seq!['-'] + dd
                && (view.yyyy == yyyy && #[trigger] datetime_matches_YYYY(yyyy, view))
                && (view.mm == mm && datetime_matches_MM(mm, view))
                && (view.dd == dd && datetime_matches_DD(dd, view));
    let mm = choose|mm: Seq<char>|
        exists|dd: Seq<char>|
            date == yyyy + seq!['-'] + mm + seq!['-'] + dd
                && (view.yyyy == yyyy && datetime_matches_YYYY(yyyy, view))
                && (view.mm == mm && #[trigger] datetime_matches_MM(mm, view))
                && (view.dd == dd && datetime_matches_DD(dd, view));
    let dd = choose|dd: Seq<char>|
        date == yyyy + seq!['-'] + mm + seq!['-'] + dd
            && (view.yyyy == yyyy && datetime_matches_YYYY(yyyy, view))
            && (view.mm == mm && datetime_matches_MM(mm, view))
            && (view.dd == dd && #[trigger] datetime_matches_DD(dd, view));
    reveal(datetime_matches_YYYY);
    reveal(datetime_matches_MM);
    reveal(datetime_matches_DD);
    assert(yyyy.len() == 4);
    assert(mm.len() == 2);
    assert(dd.len() == 2);
    assert forall|index: int| 0 <= index < yyyy.len() implies
        #[trigger] triptych_is_digit(yyyy[index]) by {
    }
    assert forall|index: int| 0 <= index < mm.len() implies
        #[trigger] triptych_is_digit(mm[index]) by {
    }
    assert forall|index: int| 0 <= index < dd.len() implies
        #[trigger] triptych_is_digit(dd[index]) by {
    }
    datetime_four_digit_capture_value(yyyy);
    datetime_two_digit_capture_value(mm);
    datetime_two_digit_capture_value(dd);
    assert(date.len() == 10);
    assert(date[0] == yyyy[0]);
    assert(date[1] == yyyy[1]);
    assert(date[2] == yyyy[2]);
    assert(date[3] == yyyy[3]);
    assert(date[4] == '-');
    assert(date[5] == mm[0]);
    assert(date[6] == mm[1]);
    assert(date[7] == '-');
    assert(date[8] == dd[0]);
    assert(date[9] == dd[1]);
    reveal(datetime_four_digits);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
}

pub proof fn datetime_time_capture_facts(time: Seq<char>, view: DatetimeView)
    requires
        datetime_matches_Time(time, view),
    ensures
        time.len() == 8,
        time[2] == ':',
        time[5] == ':',
        datetime_two_digits(time, 0) == Some(triptych_nat_of(view.time_hh)),
        datetime_two_digits(time, 3) == Some(triptych_nat_of(view.time_mm)),
        datetime_two_digits(time, 6) == Some(triptych_nat_of(view.ss)),
{
    reveal(datetime_matches_Time);
    let hh = choose|hh: Seq<char>|
        exists|mm: Seq<char>, ss: Seq<char>|
            time == hh + seq![':'] + mm + seq![':'] + ss
                && (view.time_hh == hh && #[trigger] datetime_matches_hh(hh, view))
                && (view.time_mm == mm && datetime_matches_mm(mm, view))
                && (view.ss == ss && datetime_matches_ss(ss, view));
    let mm = choose|mm: Seq<char>|
        exists|ss: Seq<char>|
            time == hh + seq![':'] + mm + seq![':'] + ss
                && (view.time_hh == hh && datetime_matches_hh(hh, view))
                && (view.time_mm == mm && #[trigger] datetime_matches_mm(mm, view))
                && (view.ss == ss && datetime_matches_ss(ss, view));
    let ss = choose|ss: Seq<char>|
        time == hh + seq![':'] + mm + seq![':'] + ss
            && (view.time_hh == hh && datetime_matches_hh(hh, view))
            && (view.time_mm == mm && datetime_matches_mm(mm, view))
            && (view.ss == ss && #[trigger] datetime_matches_ss(ss, view));
    reveal(datetime_matches_hh);
    reveal(datetime_matches_mm);
    reveal(datetime_matches_ss);
    assert(hh.len() == 2);
    assert(mm.len() == 2);
    assert(ss.len() == 2);
    assert forall|index: int| 0 <= index < hh.len() implies
        #[trigger] triptych_is_digit(hh[index]) by {
    }
    assert forall|index: int| 0 <= index < mm.len() implies
        #[trigger] triptych_is_digit(mm[index]) by {
    }
    assert forall|index: int| 0 <= index < ss.len() implies
        #[trigger] triptych_is_digit(ss[index]) by {
    }
    datetime_two_digit_capture_value(hh);
    datetime_two_digit_capture_value(mm);
    datetime_two_digit_capture_value(ss);
    assert(time.len() == 8);
    assert(time[0] == hh[0]);
    assert(time[1] == hh[1]);
    assert(time[2] == ':');
    assert(time[3] == mm[0]);
    assert(time[4] == mm[1]);
    assert(time[5] == ':');
    assert(time[6] == ss[0]);
    assert(time[7] == ss[1]);
    reveal(datetime_two_digits);
    reveal(datetime_digit);
}

pub proof fn datetime_sss_capture_facts(sss: Seq<char>, view: DatetimeView)
    requires
        datetime_matches_SSS(sss, view),
    ensures
        sss.len() == 3,
        datetime_three_digits(sss, 0) == Some(triptych_nat_of(sss)),
{
    reveal(datetime_matches_SSS);
    assert forall|index: int| 0 <= index < sss.len() implies
        #[trigger] triptych_is_digit(sss[index]) by {
    }
    datetime_three_digit_capture_value(sss);
}

pub proof fn datetime_offset_capture_facts(offset: Seq<char>, view: DatetimeView)
    requires
        datetime_matches_Offset(offset, view),
    ensures
        offset.len() == 5,
        offset[0] == '+' || offset[0] == '-',
        datetime_two_digits(offset, 1) == Some(triptych_nat_of(view.offset_hh)),
        datetime_two_digits(offset, 3) == Some(triptych_nat_of(view.offset_mm)),
{
    reveal(datetime_matches_Offset);
    if exists|hh: Seq<char>, mm: Seq<char>|
        offset == seq!['+'] + hh + mm
            && (view.offset_hh == hh && datetime_matches_hh(hh, view))
            && (view.offset_mm == mm && datetime_matches_mm(mm, view)) {
        let hh = choose|hh: Seq<char>|
            exists|mm: Seq<char>|
                offset == seq!['+'] + hh + mm
                    && (view.offset_hh == hh
                        && #[trigger] datetime_matches_hh(hh, view))
                    && (view.offset_mm == mm && datetime_matches_mm(mm, view));
        let mm = choose|mm: Seq<char>|
            offset == seq!['+'] + hh + mm
                && (view.offset_hh == hh && datetime_matches_hh(hh, view))
                && (view.offset_mm == mm
                    && #[trigger] datetime_matches_mm(mm, view));
        reveal(datetime_matches_hh);
        reveal(datetime_matches_mm);
        assert(hh.len() == 2);
        assert(mm.len() == 2);
        assert forall|index: int| 0 <= index < hh.len() implies
            #[trigger] triptych_is_digit(hh[index]) by {
        }
        assert forall|index: int| 0 <= index < mm.len() implies
            #[trigger] triptych_is_digit(mm[index]) by {
        }
        datetime_two_digit_capture_value(hh);
        datetime_two_digit_capture_value(mm);
        assert(offset.len() == 5);
        assert(offset[0] == '+');
        assert(offset[1] == hh[0]);
        assert(offset[2] == hh[1]);
        assert(offset[3] == mm[0]);
        assert(offset[4] == mm[1]);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    } else {
        let hh = choose|hh: Seq<char>|
            exists|mm: Seq<char>|
                offset == seq!['-'] + hh + mm
                    && (view.offset_hh == hh
                        && #[trigger] datetime_matches_hh(hh, view))
                    && (view.offset_mm == mm && datetime_matches_mm(mm, view));
        let mm = choose|mm: Seq<char>|
            offset == seq!['-'] + hh + mm
                && (view.offset_hh == hh && datetime_matches_hh(hh, view))
                && (view.offset_mm == mm
                    && #[trigger] datetime_matches_mm(mm, view));
        reveal(datetime_matches_hh);
        reveal(datetime_matches_mm);
        assert(hh.len() == 2);
        assert(mm.len() == 2);
        assert forall|index: int| 0 <= index < hh.len() implies
            #[trigger] triptych_is_digit(hh[index]) by {
        }
        assert forall|index: int| 0 <= index < mm.len() implies
            #[trigger] triptych_is_digit(mm[index]) by {
        }
        datetime_two_digit_capture_value(hh);
        datetime_two_digit_capture_value(mm);
        assert(offset.len() == 5);
        assert(offset[0] == '-');
        assert(offset[1] == hh[0]);
        assert(offset[2] == hh[1]);
        assert(offset[3] == mm[0]);
        assert(offset[4] == mm[1]);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
}

pub proof fn datetime_view_field_bounds(view: DatetimeView)
    requires
        datetime_view_wf_constraints(view),
    ensures
        datetime_valid_date(
            triptych_nat_of(view.yyyy),
            triptych_nat_of(view.mm),
            triptych_nat_of(view.dd),
        ),
        0 <= triptych_nat_of(view.time_hh) < 24,
        0 <= triptych_nat_of(view.time_mm) < 60,
        0 <= triptych_nat_of(view.ss) < 60,
        0 <= triptych_nat_of(view.offset_hh) < 24,
        0 <= triptych_nat_of(view.offset_mm) < 60,
{
    reveal(datetime_view_wf_constraints);
    reveal(datetime_wf_constraints);
    reveal(datetime_valid_date);
    reveal(datetime_days_in_month);
    reveal(datetime_is_leap_year);
}

pub proof fn datetime_parsed_fields_imply_view_wf(
    view: DatetimeView,
    year: int,
    month: int,
    day: int,
    hour: int,
    minute: int,
    second: int,
    offset_hour: int,
    offset_minute: int,
)
    requires
        triptych_nat_of(view.yyyy) == year,
        triptych_nat_of(view.mm) == month,
        triptych_nat_of(view.dd) == day,
        triptych_nat_of(view.time_hh) == hour,
        triptych_nat_of(view.time_mm) == minute,
        triptych_nat_of(view.ss) == second,
        triptych_nat_of(view.offset_hh) == offset_hour,
        triptych_nat_of(view.offset_mm) == offset_minute,
        datetime_valid_date(year, month, day),
        0 <= hour < 24,
        0 <= minute < 60,
        0 <= second < 60,
        0 <= offset_hour < 24,
        0 <= offset_minute < 60,
    ensures
        datetime_view_wf_constraints(view),
{
    reveal(datetime_view_wf_constraints);
    reveal(datetime_wf_constraints);
    reveal(datetime_valid_date);
    reveal(datetime_days_in_month);
    reveal(datetime_is_leap_year);
}

pub proof fn datetime_view_denotation_as_epoch(view: DatetimeView)
    ensures
        datetime_view_denotation(view) == datetime_epoch_millis(
            triptych_nat_of(view.yyyy),
            triptych_nat_of(view.mm),
            triptych_nat_of(view.dd),
            triptych_nat_of(view.time_hh),
            triptych_nat_of(view.time_mm),
            triptych_nat_of(view.ss),
            triptych_nat_of(view.sss),
            triptych_sign_of(view.offset) * (
                triptych_nat_of(view.offset_hh) * 3_600
                    + triptych_nat_of(view.offset_mm) * 60
            ),
        ),
{
    reveal(datetime_view_denotation);
    reveal(datetime_value);
    reveal(datetime_epoch_millis);
    reveal(datetime_days_from_civil);
    assert(
        triptych_sign_of(view.offset) * (
            triptych_nat_of(view.offset_hh) * 3_600_000
                + triptych_nat_of(view.offset_mm) * 60_000
        ) == triptych_sign_of(view.offset) * (
            triptych_nat_of(view.offset_hh) * 3_600
                + triptych_nat_of(view.offset_mm) * 60
        ) * 1_000
    );
}

pub proof fn datetime_finish_soundness(
    input: Seq<char>,
    value: int,
    view: DatetimeView,
)
    requires
        datetime_matches_view(input, view),
        datetime_is_wf_Datetime(input),
        datetime_view_wf_constraints(view),
        datetime_view_denotation(view) == value,
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        datetime_is_valid(input),
        datetime_matches_result(input, value),
{
    assert(datetime_view_constraints(view)) by {
        reveal(datetime_view_constraints);
        reveal(datetime_constraints);
        reveal(datetime_view_denotation);
    }
    assert(datetime_view_valid(view)) by {
        reveal(datetime_view_valid);
    }
    assert(datetime_matches_result(input, value)) by {
        reveal(datetime_matches_result);
        assert(exists|candidate: DatetimeView|
            datetime_matches_view(input, candidate)
                && datetime_view_valid(candidate)
                && datetime_view_denotation(candidate) == value) by {
            assert(
                datetime_matches_view(input, view)
                    && datetime_view_valid(view)
                    && datetime_view_denotation(view) == value
            );
        }
    }
    assert(datetime_satisfies_wf_constraints(input)) by {
        reveal(datetime_satisfies_wf_constraints);
        assert(exists|candidate: DatetimeView|
            datetime_matches_view(input, candidate)
                && datetime_view_wf_constraints(candidate)) by {
            assert(
                datetime_matches_view(input, view)
                    && datetime_view_wf_constraints(view)
            );
        }
    }
    assert(datetime_satisfies_constraints(input)) by {
        reveal(datetime_satisfies_constraints);
        assert(exists|candidate: DatetimeView|
            datetime_matches_view(input, candidate)
                && datetime_view_constraints(candidate)) by {
            assert(
                datetime_matches_view(input, view)
                    && datetime_view_constraints(view)
            );
        }
    }
    reveal(datetime_is_valid);
    reveal(datetime_is_wf);
}

pub proof fn datetime_date_only_parse_sound(
    input: Seq<char>,
    value: int,
    year: int,
    month: int,
    day: int,
)
    requires
        input.len() == 10,
        input[4] == '-',
        input[7] == '-',
        datetime_four_digits(input, 0) == Some(year),
        datetime_two_digits(input, 5) == Some(month),
        datetime_two_digits(input, 8) == Some(day),
        datetime_valid_date(year, month, day),
        value == datetime_epoch_millis(year, month, day, 0, 0, 0, 0, 0),
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        datetime_is_valid(input),
        datetime_matches_result(input, value),
{
    let empty = Seq::<char>::empty();
    let date = input.subrange(0, 10);
    let view = DatetimeView {
        input,
        yyyy: input.subrange(0, 4),
        mm: input.subrange(5, 7),
        dd: input.subrange(8, 10),
        time_hh: empty,
        time_mm: empty,
        ss: empty,
        sss: empty,
        offset: empty,
        offset_hh: empty,
        offset_mm: empty,
    };
    datetime_date_subranges_match(input, view, year, month, day);
    assert(input == date) by {
        assert_seqs_equal!(input == date);
    }
    assert(datetime_matches_Datetime(input, view)) by {
        reveal(datetime_matches_Datetime);
        assert(exists|candidate_date: Seq<char>|
            input == candidate_date
                && datetime_matches_Date(candidate_date, view)
                && view.time_hh == seq![]
                && view.time_mm == seq![]
                && view.ss == seq![]
                && view.sss == seq![]
                && view.offset == seq![]
                && view.offset_hh == seq![]
                && view.offset_mm == seq![]) by {
            assert(
                input == date
                    && datetime_matches_Date(date, view)
                    && view.time_hh == seq![]
                    && view.time_mm == seq![]
                    && view.ss == seq![]
                    && view.sss == seq![]
                    && view.offset == seq![]
                    && view.offset_hh == seq![]
                    && view.offset_mm == seq![]
            );
        }
    }
    assert(datetime_matches_view(input, view)) by {
        reveal(datetime_matches_view);
    }
    assert(datetime_is_wf_Datetime(input)) by {
        reveal(datetime_is_wf_Datetime);
        assert(exists|candidate_date: Seq<char>|
            input == candidate_date && datetime_is_wf_Date(candidate_date)) by {
            assert(input == date && datetime_is_wf_Date(date));
        }
    }
    assert(triptych_nat_of(empty) == 0) by {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    datetime_parsed_fields_imply_view_wf(
        view,
        year,
        month,
        day,
        0,
        0,
        0,
        0,
        0,
    );
    datetime_view_denotation_as_epoch(view);
    assert(triptych_sign_of(empty) == 1) by {
        reveal(triptych_sign_of);
    }
    assert(datetime_view_denotation(view) == value);
    datetime_finish_soundness(input, value, view);
}

pub proof fn datetime_time_z_parse_sound(
    input: Seq<char>,
    value: int,
    year: int,
    month: int,
    day: int,
    hour: int,
    minute: int,
    second: int,
)
    requires
        input.len() == 20,
        input[4] == '-',
        input[7] == '-',
        input[10] == 'T',
        input[13] == ':',
        input[16] == ':',
        input[19] == 'Z',
        datetime_four_digits(input, 0) == Some(year),
        datetime_two_digits(input, 5) == Some(month),
        datetime_two_digits(input, 8) == Some(day),
        datetime_two_digits(input, 11) == Some(hour),
        datetime_two_digits(input, 14) == Some(minute),
        datetime_two_digits(input, 17) == Some(second),
        datetime_valid_date(year, month, day),
        0 <= hour < 24,
        0 <= minute < 60,
        0 <= second < 60,
        value == datetime_epoch_millis(
            year,
            month,
            day,
            hour,
            minute,
            second,
            0,
            0,
        ),
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        datetime_is_valid(input),
        datetime_matches_result(input, value),
{
    let empty = Seq::<char>::empty();
    let date = input.subrange(0, 10);
    let time = input.subrange(11, 19);
    let view = DatetimeView {
        input,
        yyyy: input.subrange(0, 4),
        mm: input.subrange(5, 7),
        dd: input.subrange(8, 10),
        time_hh: input.subrange(11, 13),
        time_mm: input.subrange(14, 16),
        ss: input.subrange(17, 19),
        sss: empty,
        offset: empty,
        offset_hh: empty,
        offset_mm: empty,
    };
    datetime_date_subranges_match(input, view, year, month, day);
    datetime_time_subranges_match(input, view, hour, minute, second);
    assert(input == date + seq!['T'] + time + seq!['Z']) by {
        assert_seqs_equal!(input == date + seq!['T'] + time + seq!['Z']);
    }
    assert(datetime_matches_Datetime(input, view)) by {
        reveal(datetime_matches_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>|
            input == candidate_date + seq!['T'] + candidate_time + seq!['Z']
                && datetime_matches_Date(candidate_date, view)
                && datetime_matches_Time(candidate_time, view)
                && view.sss == seq![]
                && view.offset == seq![]
                && view.offset_hh == seq![]
                && view.offset_mm == seq![]) by {
            assert(
                input == date + seq!['T'] + time + seq!['Z']
                    && datetime_matches_Date(date, view)
                    && datetime_matches_Time(time, view)
                    && view.sss == seq![]
                    && view.offset == seq![]
                    && view.offset_hh == seq![]
                    && view.offset_mm == seq![]
            );
        }
    }
    assert(datetime_matches_view(input, view)) by {
        reveal(datetime_matches_view);
    }
    assert(datetime_is_wf_Datetime(input)) by {
        reveal(datetime_is_wf_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>|
            input == candidate_date + seq!['T'] + candidate_time + seq!['Z']
                && datetime_is_wf_Date(candidate_date)
                && datetime_is_wf_Time(candidate_time)) by {
            assert(
                input == date + seq!['T'] + time + seq!['Z']
                    && datetime_is_wf_Date(date)
                    && datetime_is_wf_Time(time)
            );
        }
    }
    assert(triptych_nat_of(empty) == 0) by {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    datetime_parsed_fields_imply_view_wf(
        view,
        year,
        month,
        day,
        hour,
        minute,
        second,
        0,
        0,
    );
    datetime_view_denotation_as_epoch(view);
    assert(triptych_sign_of(empty) == 1) by {
        reveal(triptych_sign_of);
    }
    assert(datetime_view_denotation(view) == value);
    datetime_finish_soundness(input, value, view);
}

pub proof fn datetime_millis_z_parse_sound(
    input: Seq<char>,
    value: int,
    year: int,
    month: int,
    day: int,
    hour: int,
    minute: int,
    second: int,
    millisecond: int,
)
    requires
        input.len() == 24,
        input[4] == '-',
        input[7] == '-',
        input[10] == 'T',
        input[13] == ':',
        input[16] == ':',
        input[19] == '.',
        input[23] == 'Z',
        datetime_four_digits(input, 0) == Some(year),
        datetime_two_digits(input, 5) == Some(month),
        datetime_two_digits(input, 8) == Some(day),
        datetime_two_digits(input, 11) == Some(hour),
        datetime_two_digits(input, 14) == Some(minute),
        datetime_two_digits(input, 17) == Some(second),
        datetime_three_digits(input, 20) == Some(millisecond),
        datetime_valid_date(year, month, day),
        0 <= hour < 24,
        0 <= minute < 60,
        0 <= second < 60,
        value == datetime_epoch_millis(
            year,
            month,
            day,
            hour,
            minute,
            second,
            millisecond,
            0,
        ),
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        datetime_is_valid(input),
        datetime_matches_result(input, value),
{
    let empty = Seq::<char>::empty();
    let date = input.subrange(0, 10);
    let time = input.subrange(11, 19);
    let sss = input.subrange(20, 23);
    let view = DatetimeView {
        input,
        yyyy: input.subrange(0, 4),
        mm: input.subrange(5, 7),
        dd: input.subrange(8, 10),
        time_hh: input.subrange(11, 13),
        time_mm: input.subrange(14, 16),
        ss: input.subrange(17, 19),
        sss,
        offset: empty,
        offset_hh: empty,
        offset_mm: empty,
    };
    datetime_date_subranges_match(input, view, year, month, day);
    datetime_time_subranges_match(input, view, hour, minute, second);
    datetime_sss_subrange_matches(input, view, millisecond);
    assert(input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']) by {
        assert_seqs_equal!(
            input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']
        );
    }
    assert(datetime_matches_Datetime(input, view)) by {
        reveal(datetime_matches_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>,
                candidate_sss: Seq<char>|
            input
                == candidate_date
                    + seq!['T']
                    + candidate_time
                    + seq!['.']
                    + candidate_sss
                    + seq!['Z']
                && datetime_matches_Date(candidate_date, view)
                && datetime_matches_Time(candidate_time, view)
                && (view.sss == candidate_sss
                    && datetime_matches_SSS(candidate_sss, view))
                && view.offset == seq![]
                && view.offset_hh == seq![]
                && view.offset_mm == seq![]) by {
            assert(
                input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']
                    && datetime_matches_Date(date, view)
                    && datetime_matches_Time(time, view)
                    && (view.sss == sss && datetime_matches_SSS(sss, view))
                    && view.offset == seq![]
                    && view.offset_hh == seq![]
                    && view.offset_mm == seq![]
            );
        }
    }
    assert(datetime_matches_view(input, view)) by {
        reveal(datetime_matches_view);
    }
    assert(datetime_is_wf_Datetime(input)) by {
        reveal(datetime_is_wf_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>,
                candidate_sss: Seq<char>|
            input
                == candidate_date
                    + seq!['T']
                    + candidate_time
                    + seq!['.']
                    + candidate_sss
                    + seq!['Z']
                && datetime_is_wf_Date(candidate_date)
                && datetime_is_wf_Time(candidate_time)
                && datetime_is_wf_SSS(candidate_sss)) by {
            assert(
                input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']
                    && datetime_is_wf_Date(date)
                    && datetime_is_wf_Time(time)
                    && datetime_is_wf_SSS(sss)
            );
        }
    }
    assert(triptych_nat_of(empty) == 0) by {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    datetime_parsed_fields_imply_view_wf(
        view,
        year,
        month,
        day,
        hour,
        minute,
        second,
        0,
        0,
    );
    datetime_view_denotation_as_epoch(view);
    assert(triptych_sign_of(empty) == 1) by {
        reveal(triptych_sign_of);
    }
    assert(datetime_view_denotation(view) == value);
    datetime_finish_soundness(input, value, view);
}

pub proof fn datetime_time_offset_parse_sound(
    input: Seq<char>,
    value: int,
    year: int,
    month: int,
    day: int,
    hour: int,
    minute: int,
    second: int,
    offset_hour: int,
    offset_minute: int,
)
    requires
        input.len() == 24,
        input[4] == '-',
        input[7] == '-',
        input[10] == 'T',
        input[13] == ':',
        input[16] == ':',
        input[19] == '+' || input[19] == '-',
        datetime_four_digits(input, 0) == Some(year),
        datetime_two_digits(input, 5) == Some(month),
        datetime_two_digits(input, 8) == Some(day),
        datetime_two_digits(input, 11) == Some(hour),
        datetime_two_digits(input, 14) == Some(minute),
        datetime_two_digits(input, 17) == Some(second),
        datetime_two_digits(input, 20) == Some(offset_hour),
        datetime_two_digits(input, 22) == Some(offset_minute),
        datetime_valid_date(year, month, day),
        0 <= hour < 24,
        0 <= minute < 60,
        0 <= second < 60,
        0 <= offset_hour < 24,
        0 <= offset_minute < 60,
        value == datetime_epoch_millis(
            year,
            month,
            day,
            hour,
            minute,
            second,
            0,
            (if input[19] == '+' { 1 } else { -1 }) * (
                offset_hour * 3_600 + offset_minute * 60
            ),
        ),
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        datetime_is_valid(input),
        datetime_matches_result(input, value),
{
    let empty = Seq::<char>::empty();
    let date = input.subrange(0, 10);
    let time = input.subrange(11, 19);
    let offset = input.subrange(19, 24);
    let view = DatetimeView {
        input,
        yyyy: input.subrange(0, 4),
        mm: input.subrange(5, 7),
        dd: input.subrange(8, 10),
        time_hh: input.subrange(11, 13),
        time_mm: input.subrange(14, 16),
        ss: input.subrange(17, 19),
        sss: empty,
        offset,
        offset_hh: input.subrange(20, 22),
        offset_mm: input.subrange(22, 24),
    };
    datetime_date_subranges_match(input, view, year, month, day);
    datetime_time_subranges_match(input, view, hour, minute, second);
    datetime_offset_subranges_match(input, view, 19, offset_hour, offset_minute);
    assert(input == date + seq!['T'] + time + offset) by {
        assert_seqs_equal!(input == date + seq!['T'] + time + offset);
    }
    assert(datetime_matches_Datetime(input, view)) by {
        reveal(datetime_matches_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>,
                candidate_offset: Seq<char>|
            input == candidate_date + seq!['T'] + candidate_time + candidate_offset
                && datetime_matches_Date(candidate_date, view)
                && datetime_matches_Time(candidate_time, view)
                && (view.offset == candidate_offset
                    && datetime_matches_Offset(candidate_offset, view))
                && view.sss == seq![]) by {
            assert(
                input == date + seq!['T'] + time + offset
                    && datetime_matches_Date(date, view)
                    && datetime_matches_Time(time, view)
                    && (view.offset == offset
                        && datetime_matches_Offset(offset, view))
                    && view.sss == seq![]
            );
        }
    }
    assert(datetime_matches_view(input, view)) by {
        reveal(datetime_matches_view);
    }
    assert(datetime_is_wf_Datetime(input)) by {
        reveal(datetime_is_wf_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>,
                candidate_offset: Seq<char>|
            input == candidate_date + seq!['T'] + candidate_time + candidate_offset
                && datetime_is_wf_Date(candidate_date)
                && datetime_is_wf_Time(candidate_time)
                && datetime_is_wf_Offset(candidate_offset)) by {
            assert(
                input == date + seq!['T'] + time + offset
                    && datetime_is_wf_Date(date)
                    && datetime_is_wf_Time(time)
                    && datetime_is_wf_Offset(offset)
            );
        }
    }
    assert(triptych_nat_of(empty) == 0) by {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    datetime_parsed_fields_imply_view_wf(
        view,
        year,
        month,
        day,
        hour,
        minute,
        second,
        offset_hour,
        offset_minute,
    );
    datetime_view_denotation_as_epoch(view);
    assert(datetime_view_denotation(view) == value);
    datetime_finish_soundness(input, value, view);
}

pub proof fn datetime_millis_offset_parse_sound(
    input: Seq<char>,
    value: int,
    year: int,
    month: int,
    day: int,
    hour: int,
    minute: int,
    second: int,
    millisecond: int,
    offset_hour: int,
    offset_minute: int,
)
    requires
        input.len() == 28,
        input[4] == '-',
        input[7] == '-',
        input[10] == 'T',
        input[13] == ':',
        input[16] == ':',
        input[19] == '.',
        input[23] == '+' || input[23] == '-',
        datetime_four_digits(input, 0) == Some(year),
        datetime_two_digits(input, 5) == Some(month),
        datetime_two_digits(input, 8) == Some(day),
        datetime_two_digits(input, 11) == Some(hour),
        datetime_two_digits(input, 14) == Some(minute),
        datetime_two_digits(input, 17) == Some(second),
        datetime_three_digits(input, 20) == Some(millisecond),
        datetime_two_digits(input, 24) == Some(offset_hour),
        datetime_two_digits(input, 26) == Some(offset_minute),
        datetime_valid_date(year, month, day),
        0 <= hour < 24,
        0 <= minute < 60,
        0 <= second < 60,
        0 <= offset_hour < 24,
        0 <= offset_minute < 60,
        value == datetime_epoch_millis(
            year,
            month,
            day,
            hour,
            minute,
            second,
            millisecond,
            (if input[23] == '+' { 1 } else { -1 }) * (
                offset_hour * 3_600 + offset_minute * 60
            ),
        ),
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        datetime_is_valid(input),
        datetime_matches_result(input, value),
{
    let date = input.subrange(0, 10);
    let time = input.subrange(11, 19);
    let sss = input.subrange(20, 23);
    let offset = input.subrange(23, 28);
    let view = DatetimeView {
        input,
        yyyy: input.subrange(0, 4),
        mm: input.subrange(5, 7),
        dd: input.subrange(8, 10),
        time_hh: input.subrange(11, 13),
        time_mm: input.subrange(14, 16),
        ss: input.subrange(17, 19),
        sss,
        offset,
        offset_hh: input.subrange(24, 26),
        offset_mm: input.subrange(26, 28),
    };
    datetime_date_subranges_match(input, view, year, month, day);
    datetime_time_subranges_match(input, view, hour, minute, second);
    datetime_sss_subrange_matches(input, view, millisecond);
    datetime_offset_subranges_match(input, view, 23, offset_hour, offset_minute);
    assert(input == date + seq!['T'] + time + seq!['.'] + sss + offset) by {
        assert_seqs_equal!(
            input == date + seq!['T'] + time + seq!['.'] + sss + offset
        );
    }
    assert(datetime_matches_Datetime(input, view)) by {
        reveal(datetime_matches_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>,
                candidate_sss: Seq<char>, candidate_offset: Seq<char>|
            input
                == candidate_date
                    + seq!['T']
                    + candidate_time
                    + seq!['.']
                    + candidate_sss
                    + candidate_offset
                && datetime_matches_Date(candidate_date, view)
                && datetime_matches_Time(candidate_time, view)
                && (view.sss == candidate_sss
                    && datetime_matches_SSS(candidate_sss, view))
                && (view.offset == candidate_offset
                    && datetime_matches_Offset(candidate_offset, view))) by {
            assert(
                input == date + seq!['T'] + time + seq!['.'] + sss + offset
                    && datetime_matches_Date(date, view)
                    && datetime_matches_Time(time, view)
                    && (view.sss == sss && datetime_matches_SSS(sss, view))
                    && (view.offset == offset
                        && datetime_matches_Offset(offset, view))
            );
        }
    }
    assert(datetime_matches_view(input, view)) by {
        reveal(datetime_matches_view);
    }
    assert(datetime_is_wf_Datetime(input)) by {
        reveal(datetime_is_wf_Datetime);
        assert(exists|candidate_date: Seq<char>, candidate_time: Seq<char>,
                candidate_sss: Seq<char>, candidate_offset: Seq<char>|
            input
                == candidate_date
                    + seq!['T']
                    + candidate_time
                    + seq!['.']
                    + candidate_sss
                    + candidate_offset
                && datetime_is_wf_Date(candidate_date)
                && datetime_is_wf_Time(candidate_time)
                && datetime_is_wf_SSS(candidate_sss)
                && datetime_is_wf_Offset(candidate_offset)) by {
            assert(
                input == date + seq!['T'] + time + seq!['.'] + sss + offset
                    && datetime_is_wf_Date(date)
                    && datetime_is_wf_Time(time)
                    && datetime_is_wf_SSS(sss)
                    && datetime_is_wf_Offset(offset)
            );
        }
    }
    datetime_parsed_fields_imply_view_wf(
        view,
        year,
        month,
        day,
        hour,
        minute,
        second,
        offset_hour,
        offset_minute,
    );
    datetime_view_denotation_as_epoch(view);
    assert(datetime_view_denotation(view) == value);
    datetime_finish_soundness(input, value, view);
}

pub open spec fn datetime_date_only_branch(
    input: Seq<char>,
    view: DatetimeView,
) -> bool {
    exists|date: Seq<char>|
        input == date
            && #[trigger] datetime_matches_Date(date, view)
            && view.time_hh == seq![]
            && view.time_mm == seq![]
            && view.ss == seq![]
            && view.sss == seq![]
            && view.offset == seq![]
            && view.offset_hh == seq![]
            && view.offset_mm == seq![]
}

pub proof fn datetime_date_only_branch_parses(
    input: Seq<char>,
    view: DatetimeView,
)
    requires
        datetime_date_only_branch(input, view),
        datetime_view_wf_constraints(view),
    ensures
        datetime_parse_spec(input) == Some(datetime_view_denotation(view)),
{
    reveal(datetime_date_only_branch);
    let date = choose|date: Seq<char>|
        input == date
            && #[trigger] datetime_matches_Date(date, view)
            && view.time_hh == seq![]
            && view.time_mm == seq![]
            && view.ss == seq![]
            && view.sss == seq![]
            && view.offset == seq![]
            && view.offset_hh == seq![]
            && view.offset_mm == seq![];
    datetime_date_capture_facts(date, view);
    datetime_view_field_bounds(view);
    datetime_view_denotation_as_epoch(view);
    assert(datetime_view_denotation(view) == datetime_epoch_millis(
        triptych_nat_of(view.yyyy),
        triptych_nat_of(view.mm),
        triptych_nat_of(view.dd),
        0,
        0,
        0,
        0,
        0,
    )) by {
        reveal(triptych_nat_of);
        reveal(triptych_sign_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    reveal(datetime_parse_spec);
}

pub open spec fn datetime_time_z_branch(
    input: Seq<char>,
    view: DatetimeView,
) -> bool {
    exists|date: Seq<char>, time: Seq<char>|
        input == date + seq!['T'] + time + seq!['Z']
            && #[trigger] datetime_matches_Date(date, view)
            && #[trigger] datetime_matches_Time(time, view)
            && view.sss == seq![]
            && view.offset == seq![]
            && view.offset_hh == seq![]
            && view.offset_mm == seq![]
}

pub proof fn datetime_time_z_branch_parses(
    input: Seq<char>,
    view: DatetimeView,
)
    requires
        datetime_time_z_branch(input, view),
        datetime_view_wf_constraints(view),
    ensures
        datetime_parse_spec(input) == Some(datetime_view_denotation(view)),
{
    reveal(datetime_time_z_branch);
    let date = choose|date: Seq<char>|
        exists|time: Seq<char>|
            input == date + seq!['T'] + time + seq!['Z']
                && #[trigger] datetime_matches_Date(date, view)
                && datetime_matches_Time(time, view)
                && view.sss == seq![]
                && view.offset == seq![]
                && view.offset_hh == seq![]
                && view.offset_mm == seq![];
    let time = choose|time: Seq<char>|
        input == date + seq!['T'] + time + seq!['Z']
            && datetime_matches_Date(date, view)
            && #[trigger] datetime_matches_Time(time, view)
            && view.sss == seq![]
            && view.offset == seq![]
            && view.offset_hh == seq![]
            && view.offset_mm == seq![];
    datetime_date_capture_facts(date, view);
    datetime_time_capture_facts(time, view);
    datetime_view_field_bounds(view);
    datetime_view_denotation_as_epoch(view);
    assert(input.len() == 20);
    assert(input[4] == date[4]);
    assert(input[7] == date[7]);
    assert(input[10] == 'T');
    assert(input[13] == time[2]);
    assert(input[16] == time[5]);
    assert(input[19] == 'Z');
    assert(datetime_four_digits(input, 0) == Some(triptych_nat_of(view.yyyy))) by {
        reveal(datetime_four_digits);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 5) == Some(triptych_nat_of(view.mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 8) == Some(triptych_nat_of(view.dd))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 11) == Some(triptych_nat_of(view.time_hh))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 14) == Some(triptych_nat_of(view.time_mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 17) == Some(triptych_nat_of(view.ss))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_view_denotation(view) == datetime_epoch_millis(
        triptych_nat_of(view.yyyy),
        triptych_nat_of(view.mm),
        triptych_nat_of(view.dd),
        triptych_nat_of(view.time_hh),
        triptych_nat_of(view.time_mm),
        triptych_nat_of(view.ss),
        0,
        0,
    )) by {
        reveal(triptych_nat_of);
        reveal(triptych_sign_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    reveal(datetime_parse_spec);
}

pub open spec fn datetime_millis_z_branch(
    input: Seq<char>,
    view: DatetimeView,
) -> bool {
    exists|date: Seq<char>, time: Seq<char>, sss: Seq<char>|
        input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']
            && #[trigger] datetime_matches_Date(date, view)
            && #[trigger] datetime_matches_Time(time, view)
            && (view.sss == sss && #[trigger] datetime_matches_SSS(sss, view))
            && view.offset == seq![]
            && view.offset_hh == seq![]
            && view.offset_mm == seq![]
}

pub proof fn datetime_millis_z_branch_parses(
    input: Seq<char>,
    view: DatetimeView,
)
    requires
        datetime_millis_z_branch(input, view),
        datetime_view_wf_constraints(view),
    ensures
        datetime_parse_spec(input) == Some(datetime_view_denotation(view)),
{
    reveal(datetime_millis_z_branch);
    let date = choose|date: Seq<char>|
        exists|time: Seq<char>, sss: Seq<char>|
            input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']
                && #[trigger] datetime_matches_Date(date, view)
                && datetime_matches_Time(time, view)
                && (view.sss == sss && datetime_matches_SSS(sss, view))
                && view.offset == seq![]
                && view.offset_hh == seq![]
                && view.offset_mm == seq![];
    let time = choose|time: Seq<char>|
        exists|sss: Seq<char>|
            input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']
                && datetime_matches_Date(date, view)
                && #[trigger] datetime_matches_Time(time, view)
                && (view.sss == sss && datetime_matches_SSS(sss, view))
                && view.offset == seq![]
                && view.offset_hh == seq![]
                && view.offset_mm == seq![];
    let sss = choose|sss: Seq<char>|
        input == date + seq!['T'] + time + seq!['.'] + sss + seq!['Z']
            && datetime_matches_Date(date, view)
            && datetime_matches_Time(time, view)
            && (view.sss == sss && #[trigger] datetime_matches_SSS(sss, view))
            && view.offset == seq![]
            && view.offset_hh == seq![]
            && view.offset_mm == seq![];
    datetime_date_capture_facts(date, view);
    datetime_time_capture_facts(time, view);
    datetime_sss_capture_facts(sss, view);
    datetime_view_field_bounds(view);
    datetime_view_denotation_as_epoch(view);
    assert(input.len() == 24);
    assert(input[4] == date[4]);
    assert(input[7] == date[7]);
    assert(input[10] == 'T');
    assert(input[13] == time[2]);
    assert(input[16] == time[5]);
    assert(input[19] == '.');
    assert(input[23] == 'Z');
    assert(datetime_four_digits(input, 0) == Some(triptych_nat_of(view.yyyy))) by {
        reveal(datetime_four_digits);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 5) == Some(triptych_nat_of(view.mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 8) == Some(triptych_nat_of(view.dd))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 11) == Some(triptych_nat_of(view.time_hh))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 14) == Some(triptych_nat_of(view.time_mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 17) == Some(triptych_nat_of(view.ss))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_three_digits(input, 20) == Some(triptych_nat_of(view.sss))) by {
        reveal(datetime_three_digits);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_view_denotation(view) == datetime_epoch_millis(
        triptych_nat_of(view.yyyy),
        triptych_nat_of(view.mm),
        triptych_nat_of(view.dd),
        triptych_nat_of(view.time_hh),
        triptych_nat_of(view.time_mm),
        triptych_nat_of(view.ss),
        triptych_nat_of(view.sss),
        0,
    )) by {
        reveal(triptych_nat_of);
        reveal(triptych_sign_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    reveal(datetime_parse_spec);
}

pub open spec fn datetime_time_offset_branch(
    input: Seq<char>,
    view: DatetimeView,
) -> bool {
    exists|date: Seq<char>, time: Seq<char>, offset: Seq<char>|
        input == date + seq!['T'] + time + offset
            && #[trigger] datetime_matches_Date(date, view)
            && #[trigger] datetime_matches_Time(time, view)
            && (view.offset == offset
                && #[trigger] datetime_matches_Offset(offset, view))
            && view.sss == seq![]
}

pub proof fn datetime_time_offset_branch_parses(
    input: Seq<char>,
    view: DatetimeView,
)
    requires
        datetime_time_offset_branch(input, view),
        datetime_view_wf_constraints(view),
    ensures
        datetime_parse_spec(input) == Some(datetime_view_denotation(view)),
{
    reveal(datetime_time_offset_branch);
    let date = choose|date: Seq<char>|
        exists|time: Seq<char>, offset: Seq<char>|
            input == date + seq!['T'] + time + offset
                && #[trigger] datetime_matches_Date(date, view)
                && datetime_matches_Time(time, view)
                && (view.offset == offset && datetime_matches_Offset(offset, view))
                && view.sss == seq![];
    let time = choose|time: Seq<char>|
        exists|offset: Seq<char>|
            input == date + seq!['T'] + time + offset
                && datetime_matches_Date(date, view)
                && #[trigger] datetime_matches_Time(time, view)
                && (view.offset == offset && datetime_matches_Offset(offset, view))
                && view.sss == seq![];
    let offset = choose|offset: Seq<char>|
        input == date + seq!['T'] + time + offset
            && datetime_matches_Date(date, view)
            && datetime_matches_Time(time, view)
            && (view.offset == offset
                && #[trigger] datetime_matches_Offset(offset, view))
            && view.sss == seq![];
    datetime_date_capture_facts(date, view);
    datetime_time_capture_facts(time, view);
    datetime_offset_capture_facts(offset, view);
    datetime_view_field_bounds(view);
    datetime_view_denotation_as_epoch(view);
    assert(input.len() == 24);
    assert(input[4] == date[4]);
    assert(input[7] == date[7]);
    assert(input[10] == 'T');
    assert(input[13] == time[2]);
    assert(input[16] == time[5]);
    assert(input[19] == offset[0]);
    assert(datetime_four_digits(input, 0) == Some(triptych_nat_of(view.yyyy))) by {
        reveal(datetime_four_digits);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 5) == Some(triptych_nat_of(view.mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 8) == Some(triptych_nat_of(view.dd))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 11) == Some(triptych_nat_of(view.time_hh))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 14) == Some(triptych_nat_of(view.time_mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 17) == Some(triptych_nat_of(view.ss))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 20) == Some(triptych_nat_of(view.offset_hh))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 22) == Some(triptych_nat_of(view.offset_mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(triptych_sign_of(view.offset) == if input[19] == '+' { 1 } else { -1 }) by {
        reveal(triptych_sign_of);
    }
    assert(datetime_view_denotation(view) == datetime_epoch_millis(
        triptych_nat_of(view.yyyy),
        triptych_nat_of(view.mm),
        triptych_nat_of(view.dd),
        triptych_nat_of(view.time_hh),
        triptych_nat_of(view.time_mm),
        triptych_nat_of(view.ss),
        0,
        (if input[19] == '+' { 1 } else { -1 }) * (
            triptych_nat_of(view.offset_hh) * 3_600
                + triptych_nat_of(view.offset_mm) * 60
        ),
    )) by {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    reveal(datetime_parse_spec);
}

pub open spec fn datetime_millis_offset_branch(
    input: Seq<char>,
    view: DatetimeView,
) -> bool {
    exists|date: Seq<char>, time: Seq<char>, sss: Seq<char>, offset: Seq<char>|
        input == date + seq!['T'] + time + seq!['.'] + sss + offset
            && #[trigger] datetime_matches_Date(date, view)
            && #[trigger] datetime_matches_Time(time, view)
            && (view.sss == sss && #[trigger] datetime_matches_SSS(sss, view))
            && (view.offset == offset
                && #[trigger] datetime_matches_Offset(offset, view))
}

pub proof fn datetime_millis_offset_branch_parses(
    input: Seq<char>,
    view: DatetimeView,
)
    requires
        datetime_millis_offset_branch(input, view),
        datetime_view_wf_constraints(view),
    ensures
        datetime_parse_spec(input) == Some(datetime_view_denotation(view)),
{
    reveal(datetime_millis_offset_branch);
    let date = choose|date: Seq<char>|
        exists|time: Seq<char>, sss: Seq<char>, offset: Seq<char>|
            input == date + seq!['T'] + time + seq!['.'] + sss + offset
                && #[trigger] datetime_matches_Date(date, view)
                && datetime_matches_Time(time, view)
                && (view.sss == sss && datetime_matches_SSS(sss, view))
                && (view.offset == offset && datetime_matches_Offset(offset, view));
    let time = choose|time: Seq<char>|
        exists|sss: Seq<char>, offset: Seq<char>|
            input == date + seq!['T'] + time + seq!['.'] + sss + offset
                && datetime_matches_Date(date, view)
                && #[trigger] datetime_matches_Time(time, view)
                && (view.sss == sss && datetime_matches_SSS(sss, view))
                && (view.offset == offset && datetime_matches_Offset(offset, view));
    let sss = choose|sss: Seq<char>|
        exists|offset: Seq<char>|
            input == date + seq!['T'] + time + seq!['.'] + sss + offset
                && datetime_matches_Date(date, view)
                && datetime_matches_Time(time, view)
                && (view.sss == sss && #[trigger] datetime_matches_SSS(sss, view))
                && (view.offset == offset && datetime_matches_Offset(offset, view));
    let offset = choose|offset: Seq<char>|
        input == date + seq!['T'] + time + seq!['.'] + sss + offset
            && datetime_matches_Date(date, view)
            && datetime_matches_Time(time, view)
            && (view.sss == sss && datetime_matches_SSS(sss, view))
            && (view.offset == offset
                && #[trigger] datetime_matches_Offset(offset, view));
    datetime_date_capture_facts(date, view);
    datetime_time_capture_facts(time, view);
    datetime_sss_capture_facts(sss, view);
    datetime_offset_capture_facts(offset, view);
    datetime_view_field_bounds(view);
    datetime_view_denotation_as_epoch(view);
    assert(input.len() == 28);
    assert(input[4] == date[4]);
    assert(input[7] == date[7]);
    assert(input[10] == 'T');
    assert(input[13] == time[2]);
    assert(input[16] == time[5]);
    assert(input[19] == '.');
    assert(input[23] == offset[0]);
    assert(datetime_four_digits(input, 0) == Some(triptych_nat_of(view.yyyy))) by {
        reveal(datetime_four_digits);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 5) == Some(triptych_nat_of(view.mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 8) == Some(triptych_nat_of(view.dd))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 11) == Some(triptych_nat_of(view.time_hh))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 14) == Some(triptych_nat_of(view.time_mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 17) == Some(triptych_nat_of(view.ss))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_three_digits(input, 20) == Some(triptych_nat_of(view.sss))) by {
        reveal(datetime_three_digits);
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 24) == Some(triptych_nat_of(view.offset_hh))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(datetime_two_digits(input, 26) == Some(triptych_nat_of(view.offset_mm))) by {
        reveal(datetime_two_digits);
        reveal(datetime_digit);
    }
    assert(triptych_sign_of(view.offset) == if input[23] == '+' { 1 } else { -1 }) by {
        reveal(triptych_sign_of);
    }
    assert(datetime_view_denotation(view) == datetime_epoch_millis(
        triptych_nat_of(view.yyyy),
        triptych_nat_of(view.mm),
        triptych_nat_of(view.dd),
        triptych_nat_of(view.time_hh),
        triptych_nat_of(view.time_mm),
        triptych_nat_of(view.ss),
        triptych_nat_of(view.sss),
        (if input[23] == '+' { 1 } else { -1 }) * (
            triptych_nat_of(view.offset_hh) * 3_600
                + triptych_nat_of(view.offset_mm) * 60
        ),
    )) by {
        reveal(triptych_nat_of);
        reveal_with_fuel(triptych_nat_of_from, 2);
    }
    reveal(datetime_parse_spec);
}

pub proof fn datetime_wf_view_parses(input: Seq<char>, view: DatetimeView)
    requires
        datetime_matches_view(input, view),
        datetime_view_wf_constraints(view),
    ensures
        datetime_parse_spec(input) == Some(datetime_view_denotation(view)),
{
    reveal(datetime_matches_view);
    if datetime_date_only_branch(input, view) {
        datetime_date_only_branch_parses(input, view);
    } else if datetime_time_z_branch(input, view) {
        datetime_time_z_branch_parses(input, view);
    } else if datetime_millis_z_branch(input, view) {
        datetime_millis_z_branch_parses(input, view);
    } else if datetime_time_offset_branch(input, view) {
        datetime_time_offset_branch_parses(input, view);
    } else if datetime_millis_offset_branch(input, view) {
        datetime_millis_offset_branch_parses(input, view);
    } else {
        reveal(datetime_date_only_branch);
        reveal(datetime_time_z_branch);
        reveal(datetime_millis_z_branch);
        reveal(datetime_time_offset_branch);
        reveal(datetime_millis_offset_branch);
        reveal(datetime_matches_Datetime);
        assert(false);
    }
}

#[verifier::rlimit(100)]
pub proof fn datetime_parse_spec_sound(input: Seq<char>, value: int)
    requires
        datetime_parse_spec(input) == Some(value),
        -9_223_372_036_854_775_808 <= value <= 9_223_372_036_854_775_807,
    ensures
        datetime_is_valid(input),
        datetime_matches_result(input, value),
{
    reveal(datetime_parse_spec);
    assert(input.len() == 10
        || input.len() == 20
        || input.len() == 24
        || input.len() == 28);
    assert(input[4] == '-');
    assert(input[7] == '-');
    match (
        datetime_four_digits(input, 0),
        datetime_two_digits(input, 5),
        datetime_two_digits(input, 8),
    ) {
        (Some(year), Some(month), Some(day)) => {
            if !datetime_valid_date(year, month, day) {
                assert(false);
            } else if input.len() == 10 {
                datetime_date_only_parse_sound(
                    input,
                    value,
                    year,
                    month,
                    day,
                );
            } else {
                assert(input[10] == 'T');
                assert(input[13] == ':');
                assert(input[16] == ':');
                match (
                    datetime_two_digits(input, 11),
                    datetime_two_digits(input, 14),
                    datetime_two_digits(input, 17),
                ) {
                    (Some(hour), Some(minute), Some(second)) => {
                        datetime_two_digit_subrange_facts(input, 11, hour);
                        datetime_two_digit_subrange_facts(input, 14, minute);
                        datetime_two_digit_subrange_facts(input, 17, second);
                        if hour >= 24 || minute >= 60 || second >= 60 {
                            assert(false);
                        } else if input.len() == 20 && input[19] == 'Z' {
                            datetime_time_z_parse_sound(
                                input,
                                value,
                                year,
                                month,
                                day,
                                hour,
                                minute,
                                second,
                            );
                        } else if input.len() == 24
                            && input[19] == '.'
                            && input[23] == 'Z'
                        {
                            match datetime_three_digits(input, 20) {
                                Some(millisecond) => {
                                    datetime_millis_z_parse_sound(
                                        input,
                                        value,
                                        year,
                                        month,
                                        day,
                                        hour,
                                        minute,
                                        second,
                                        millisecond,
                                    );
                                },
                                None => {
                                    assert(false);
                                },
                            }
                        } else if input.len() == 24
                            && (input[19] == '+' || input[19] == '-')
                        {
                            match (
                                datetime_two_digits(input, 20),
                                datetime_two_digits(input, 22),
                            ) {
                                (Some(offset_hour), Some(offset_minute)) => {
                                    datetime_two_digit_subrange_facts(
                                        input,
                                        20,
                                        offset_hour,
                                    );
                                    datetime_two_digit_subrange_facts(
                                        input,
                                        22,
                                        offset_minute,
                                    );
                                    if offset_hour >= 24 || offset_minute >= 60 {
                                        assert(false);
                                    } else {
                                        if input[19] == '+' {
                                            assert(
                                                (if input[19] == '+' {
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                } else {
                                                    -(offset_hour * 3_600
                                                        + offset_minute * 60)
                                                }) == (
                                                    if input[19] == '+' {
                                                        1
                                                    } else {
                                                        -1
                                                    }
                                                ) * (
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                )
                                            ) by (nonlinear_arith);
                                        } else {
                                            assert(input[19] == '-');
                                            assert(
                                                (if input[19] == '+' {
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                } else {
                                                    -(offset_hour * 3_600
                                                        + offset_minute * 60)
                                                }) == (
                                                    if input[19] == '+' {
                                                        1
                                                    } else {
                                                        -1
                                                    }
                                                ) * (
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                )
                                            ) by (nonlinear_arith);
                                        }
                                        datetime_time_offset_parse_sound(
                                            input,
                                            value,
                                            year,
                                            month,
                                            day,
                                            hour,
                                            minute,
                                            second,
                                            offset_hour,
                                            offset_minute,
                                        );
                                    }
                                },
                                _ => {
                                    assert(false);
                                },
                            }
                        } else if input.len() == 28
                            && input[19] == '.'
                            && (input[23] == '+' || input[23] == '-')
                        {
                            match (
                                datetime_three_digits(input, 20),
                                datetime_two_digits(input, 24),
                                datetime_two_digits(input, 26),
                            ) {
                                (
                                    Some(millisecond),
                                    Some(offset_hour),
                                    Some(offset_minute),
                                ) => {
                                    datetime_two_digit_subrange_facts(
                                        input,
                                        24,
                                        offset_hour,
                                    );
                                    datetime_two_digit_subrange_facts(
                                        input,
                                        26,
                                        offset_minute,
                                    );
                                    if offset_hour >= 24 || offset_minute >= 60 {
                                        assert(false);
                                    } else {
                                        if input[23] == '+' {
                                            assert(
                                                (if input[23] == '+' {
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                } else {
                                                    -(offset_hour * 3_600
                                                        + offset_minute * 60)
                                                }) == (
                                                    if input[23] == '+' {
                                                        1
                                                    } else {
                                                        -1
                                                    }
                                                ) * (
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                )
                                            ) by (nonlinear_arith);
                                        } else {
                                            assert(input[23] == '-');
                                            assert(
                                                (if input[23] == '+' {
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                } else {
                                                    -(offset_hour * 3_600
                                                        + offset_minute * 60)
                                                }) == (
                                                    if input[23] == '+' {
                                                        1
                                                    } else {
                                                        -1
                                                    }
                                                ) * (
                                                    offset_hour * 3_600
                                                        + offset_minute * 60
                                                )
                                            ) by (nonlinear_arith);
                                        }
                                        datetime_millis_offset_parse_sound(
                                            input,
                                            value,
                                            year,
                                            month,
                                            day,
                                            hour,
                                            minute,
                                            second,
                                            millisecond,
                                            offset_hour,
                                            offset_minute,
                                        );
                                    }
                                },
                                _ => {
                                    assert(false);
                                },
                            }
                        } else {
                            assert(false);
                        }
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        },
        _ => {
            assert(false);
        },
    }
}

impl DatetimeExternalParserContract for DatetimeParser {
    open spec fn parse_to_spec(input: Seq<char>) -> Option<int> {
        datetime_external_parse_spec(input)
    }

    proof fn extparse_sound(input: Seq<char>, value: int) {
        reveal(datetime_external_parse_spec);
        datetime_parse_spec_sound(input, value);
    }

    proof fn extparse_complete(input: Seq<char>, value: int) {
        reveal(datetime_matches_result);
        let view = choose|view: DatetimeView|
            datetime_matches_view(input, view)
                && datetime_view_valid(view)
                && datetime_view_denotation(view) == value;
        reveal(datetime_view_valid);
        datetime_wf_view_parses(input, view);
        reveal(datetime_external_parse_spec);
    }

    #[verifier::rlimit(100)]
    proof fn extparse_reject(input: Seq<char>) {
        if Self::parse_to_spec(input).is_none() {
            if datetime_is_valid(input) {
                reveal(datetime_is_valid);
                reveal(datetime_is_wf);
                reveal(datetime_satisfies_wf_constraints);
                let view = choose|view: DatetimeView|
                    datetime_matches_view(input, view)
                        && datetime_view_wf_constraints(view);
                datetime_wf_view_parses(input, view);
                assert(false);
            }
        }
        if !datetime_is_valid(input) {
            match Self::parse_to_spec(input) {
                Some(value) => {
                    Self::extparse_sound(input, value);
                    assert(false);
                },
                None => {},
            }
        }
    }
}

} // verus!
