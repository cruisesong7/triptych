use vstd::prelude::*;
use vstd::string::StrSliceExecFns;

#[cfg(verus_only)]
use crate::model::*;

verus! {

pub struct DatetimeParser;

#[inline(always)]
fn datetime_two_digits_exec(input: &str, index: usize) -> (result: Option<u32>)
    requires
        input.is_ascii(),
        index <= usize::MAX - 2,
        index + 2 <= input@.len(),
    ensures
        match result {
            Some(value) => {
                datetime_two_digits(input@, index as int) == Some(value as int)
                    && value <= 99
            },
            None => datetime_two_digits(input@, index as int).is_none(),
        },
{
    let high = input.get_ascii(index);
    let low = input.get_ascii(index + 1);
    if high < b'0' || b'9' < high || low < b'0' || b'9' < low {
        proof {
            reveal(datetime_two_digits);
            reveal(datetime_digit);
        }
        None
    } else {
        let value = (high - b'0') as u32 * 10 + (low - b'0') as u32;
        proof {
            reveal(datetime_two_digits);
            reveal(datetime_digit);
        }
        Some(value)
    }
}

#[inline(always)]
fn datetime_three_digits_exec(input: &str, index: usize) -> (result: Option<u32>)
    requires
        input.is_ascii(),
        index <= usize::MAX - 3,
        index + 3 <= input@.len(),
    ensures
        match result {
            Some(value) => {
                datetime_three_digits(input@, index as int) == Some(value as int)
                    && value <= 999
            },
            None => datetime_three_digits(input@, index as int).is_none(),
        },
{
    let high = match datetime_two_digits_exec(input, index) {
        Some(value) => value,
        None => return None,
    };
    let byte = input.get_ascii(index + 2);
    if byte < b'0' || b'9' < byte {
        proof {
            reveal(datetime_three_digits);
            reveal(datetime_digit);
        }
        None
    } else {
        let value = high * 10 + (byte - b'0') as u32;
        proof {
            reveal(datetime_three_digits);
            reveal(datetime_digit);
            assert(value <= 999);
        }
        Some(value)
    }
}

#[inline(always)]
fn datetime_four_digits_exec(input: &str, index: usize) -> (result: Option<i64>)
    requires
        input.is_ascii(),
        index <= usize::MAX - 4,
        index + 4 <= input@.len(),
    ensures
        match result {
            Some(value) => {
                datetime_four_digits(input@, index as int) == Some(value as int)
                    && 0 <= value <= 9_999
            },
            None => datetime_four_digits(input@, index as int).is_none(),
        },
{
    let high = match datetime_two_digits_exec(input, index) {
        Some(value) => value,
        None => return None,
    };
    let low = match datetime_two_digits_exec(input, index + 2) {
        Some(value) => value,
        None => return None,
    };
    let combined = high * 100 + low;
    proof {
        reveal(datetime_four_digits);
        assert(high <= 99);
        assert(low <= 99);
        assert(datetime_two_digits(input@, index as int) == Some(high as int));
        assert(datetime_two_digits(input@, index as int + 2) == Some(low as int));
        assert(combined <= 9_999);
    }
    Some(combined as i64)
}

#[inline(always)]
fn datetime_is_leap_year_exec(year: i64) -> (result: bool)
    ensures
        result == datetime_is_leap_year(year as int),
{
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

#[inline(always)]
fn datetime_valid_date_exec(year: i64, month: u32, day: u32) -> (result: bool)
    ensures
        result == datetime_valid_date(year as int, month as int, day as int),
{
    let days = match month {
        4 | 6 | 9 | 11 => 30,
        2 => if datetime_is_leap_year_exec(year) { 29 } else { 28 },
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        _ => return false,
    };
    proof {
        reveal(datetime_valid_date);
        reveal(datetime_days_in_month);
    }
    1 <= day && day <= days
}

#[inline(always)]
fn datetime_days_from_civil_exec(year: i64, month: u32, day: u32) -> (result: i64)
    requires
        0 <= year <= 9_999,
        1 <= month <= 12,
        1 <= day <= 31,
    ensures
        result as int == datetime_days_from_civil(year as int, month as int, day as int),
        -719_528 <= result <= 2_932_896,
{
    let day_i = day as i64;
    let adjusted_year = if month > 2 { year } else { year - 1 };
    let era = if adjusted_year >= 0 {
        adjusted_year / 400
    } else {
        proof {
            assert(year == 0);
            assert(adjusted_year == -1);
        }
        -1
    };
    proof {
        assert(-1 <= adjusted_year <= 9_999);
        assert(-1 <= era <= 24);
    }
    let year_of_era = adjusted_year - era * 400;
    proof {
        assert(0 <= year_of_era <= 399);
    }
    let shifted_month = if month > 2 {
        assert(3 <= month);
        (month - 3) as i64
    } else {
        assert(month <= 2);
        (month + 9) as i64
    };
    proof {
        assert(0 <= shifted_month <= 11);
    }
    let day_of_year = (153 * shifted_month + 2) / 5 + day_i - 1;
    proof {
        assert(0 <= day_of_year <= 367);
    }
    let day_of_era =
        year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    proof {
        assert(0 <= day_of_era <= 146_463);
        reveal(datetime_days_from_civil);
    }
    let result = era * 146_097 + day_of_era - 719_468;
    proof {
        assert(-719_528 <= result <= 2_932_896);
    }
    result
}

impl DatetimeParser {
    #[inline]
    #[verifier::rlimit(100)]
    pub fn parse(input: &str) -> (result: Option<i64>)
        ensures
            match result {
                Some(value) => {
                    datetime_parse_spec(input@) == Some(value as int)
                        && datetime_external_parse_spec(input@) == Some(value as int)
                },
                None => {
                    datetime_parse_spec(input@).is_none()
                        && datetime_external_parse_spec(input@).is_none()
                },
            },
    {
        if !input.is_ascii() {
            proof {
                reveal(datetime_parse_spec);
                reveal(datetime_four_digits);
                reveal(datetime_two_digits);
                reveal(datetime_digit);
            }
            return None;
        }
        let length = input.unicode_len();
        if !(length == 10 || length == 20 || length == 24 || length == 28)
            || input.get_ascii(4) != b'-'
            || input.get_ascii(7) != b'-'
        {
            proof {
                reveal(datetime_parse_spec);
            }
            return None;
        }

        let year = match datetime_four_digits_exec(input, 0) {
            Some(value) => value,
            None => {
                proof {
                    reveal(datetime_parse_spec);
                }
                return None;
            },
        };
        let month = match datetime_two_digits_exec(input, 5) {
            Some(value) => value,
            None => {
                proof {
                    reveal(datetime_parse_spec);
                }
                return None;
            },
        };
        let day = match datetime_two_digits_exec(input, 8) {
            Some(value) => value,
            None => {
                proof {
                    reveal(datetime_parse_spec);
                }
                return None;
            },
        };
        if !datetime_valid_date_exec(year, month, day) {
            proof {
                reveal(datetime_parse_spec);
            }
            return None;
        }

        let mut hour = 0u32;
        let mut minute = 0u32;
        let mut second = 0u32;
        let mut millisecond = 0u32;
        let mut offset_seconds = 0i64;

        if length != 10 {
            if input.get_ascii(10) != b'T'
                || input.get_ascii(13) != b':'
                || input.get_ascii(16) != b':'
            {
                proof {
                    reveal(datetime_parse_spec);
                }
                return None;
            }
            hour = match datetime_two_digits_exec(input, 11) {
                Some(value) => value,
                None => {
                    proof {
                        reveal(datetime_parse_spec);
                    }
                    return None;
                },
            };
            minute = match datetime_two_digits_exec(input, 14) {
                Some(value) => value,
                None => {
                    proof {
                        reveal(datetime_parse_spec);
                    }
                    return None;
                },
            };
            second = match datetime_two_digits_exec(input, 17) {
                Some(value) => value,
                None => {
                    proof {
                        reveal(datetime_parse_spec);
                    }
                    return None;
                },
            };
            if hour >= 24 || minute >= 60 || second >= 60 {
                proof {
                    reveal(datetime_parse_spec);
                }
                return None;
            }

            if length == 20 && input.get_ascii(19) == b'Z' {
            } else if length == 24
                && input.get_ascii(19) == b'.'
                && input.get_ascii(23) == b'Z'
            {
                millisecond = match datetime_three_digits_exec(input, 20) {
                    Some(value) => value,
                    None => {
                        proof {
                            reveal(datetime_parse_spec);
                        }
                        return None;
                    },
                };
            } else if length == 24
                && (input.get_ascii(19) == b'+' || input.get_ascii(19) == b'-')
            {
                let offset_hour = match datetime_two_digits_exec(input, 20) {
                    Some(value) => value,
                    None => {
                        proof {
                            reveal(datetime_parse_spec);
                        }
                        return None;
                    },
                };
                let offset_minute = match datetime_two_digits_exec(input, 22) {
                    Some(value) => value,
                    None => {
                        proof {
                            reveal(datetime_parse_spec);
                        }
                        return None;
                    },
                };
                if offset_hour >= 24 || offset_minute >= 60 {
                    proof {
                        reveal(datetime_parse_spec);
                    }
                    return None;
                }
                assert(offset_hour < 24);
                assert(offset_minute < 60);
                let magnitude_u32 = offset_hour * 3_600 + offset_minute * 60;
                let magnitude = magnitude_u32 as i64;
                assert(magnitude <= 86_340);
                offset_seconds =
                    if input.get_ascii(19) == b'+' { magnitude } else { -magnitude };
            } else if length == 28
                && input.get_ascii(19) == b'.'
                && (input.get_ascii(23) == b'+' || input.get_ascii(23) == b'-')
            {
                millisecond = match datetime_three_digits_exec(input, 20) {
                    Some(value) => value,
                    None => {
                        proof {
                            reveal(datetime_parse_spec);
                        }
                        return None;
                    },
                };
                let offset_hour = match datetime_two_digits_exec(input, 24) {
                    Some(value) => value,
                    None => {
                        proof {
                            reveal(datetime_parse_spec);
                        }
                        return None;
                    },
                };
                let offset_minute = match datetime_two_digits_exec(input, 26) {
                    Some(value) => value,
                    None => {
                        proof {
                            reveal(datetime_parse_spec);
                        }
                        return None;
                    },
                };
                if offset_hour >= 24 || offset_minute >= 60 {
                    proof {
                        reveal(datetime_parse_spec);
                    }
                    return None;
                }
                assert(offset_hour < 24);
                assert(offset_minute < 60);
                let magnitude_u32 = offset_hour * 3_600 + offset_minute * 60;
                let magnitude = magnitude_u32 as i64;
                assert(magnitude <= 86_340);
                offset_seconds =
                    if input.get_ascii(23) == b'+' { magnitude } else { -magnitude };
            } else {
                proof {
                    reveal(datetime_parse_spec);
                }
                return None;
            }
        }

        let days = datetime_days_from_civil_exec(year, month, day);
        assert(-719_528 <= days <= 2_932_896);
        assert(hour < 24);
        assert(minute < 60);
        assert(second < 60);
        assert(millisecond <= 999);
        assert(-86_340 <= offset_seconds <= 86_340);
        let local_seconds = days * 86_400
            + hour as i64 * 3_600
            + minute as i64 * 60
            + second as i64;
        assert(-62_167_219_200 <= local_seconds <= 253_402_300_799);
        let value =
            (local_seconds - offset_seconds) * 1_000 + millisecond as i64;
        proof {
            reveal(datetime_epoch_millis);
            reveal(datetime_parse_spec);
            reveal(datetime_external_parse_spec);
        }
        Some(value)
    }
}

} // verus!
