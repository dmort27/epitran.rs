use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{anychar, one_of},
    combinator::{map_res, recognize},
    multi::{many0, many1},
    sequence::preceded,
    Err, IResult, Parser,
};

pub fn get_graphemes(input: &str) -> Vec<String> {
    let (_, chars) = parse_grapheme_sequence(input).unwrap_or(("", Vec::new()));
    chars.iter().map(|c| c.to_string()).collect()
}

fn parse_grapheme_sequence(input: &str) -> IResult<&str, Vec<char>> {
    let mut parser = many0(alt((uni_esc, anychar)));
    let (input, chars) = parser.parse(input)?;
    Ok((input, chars))
}

fn uni_esc(input: &str) -> IResult<&str, char> {
    let mut parser = map_res(
        preceded(
            tag("\\u"),
            recognize(many1(one_of("0123456789abcdefABCDEF"))),
        ),
        |out: &str| u32::from_str_radix(out, 16),
    );
    let (input, num) = parser.parse(input)?;
    let c = std::char::from_u32(num).unwrap();
    Ok((input, c))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_graphemes() {
        assert_eq!(get_graphemes("abc"), vec!["a", "b", "c"]);
    }
    fn test_get_graphemes_with_uni_esc() {
        assert_eq!(get_graphemes("k\\u0250t"), vec!["k", "ɐ", "t"]);
    }
}
