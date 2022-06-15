use nom::{
    character::complete::{char, line_ending, none_of, space1},
    combinator::{map_res, recognize, success},
    multi::{many0, many1, separated_list1},
    sequence::{preceded, tuple, delimited, terminated},
    branch::alt,
    IResult,
};

#[derive(Debug, PartialEq)]
enum RegexAST {
    String(String),
    Group(Vec<RegexAST>),
    Option(Box<RegexAST>),
    Star(Box<RegexAST>),
    Plus(Box<RegexAST>),
    Disjunction(Vec<RegexAST>),
    Class(Vec<char>),
    ClassComplement(Vec<char>),
    Epsilon,
}

#[derive(Debug, PartialEq)]
struct RewriteRule {
    left: RegexAST,
    right: RegexAST,
    source: RegexAST,
    target: String,
}

fn string(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = many1(none_of(" ()|*+^"))(input)?;
    Ok((input, RegexAST::String(s.into_iter().collect::<String>())))
}

fn class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(char('['), many1(none_of(" ()|*+^")), char(']'))(input)?;
    Ok((input, RegexAST::Class(s)))
}

fn complement_class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(char('['), preceded(char('^'), many1(none_of(" ()|*+~"))), char(']'))(input)?;
    Ok((input, RegexAST::ClassComplement(s)))
}

fn epsilon(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = success("")(input)?;
    Ok((input, RegexAST::Epsilon))
}

fn sequence(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = many0(alt((string, class, complement_class, epsilon, disjunction, plus, star, option)))(input)?;
    Ok((input, RegexAST::Group(g)))
}

fn group(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = delimited(char('('), sequence, char(')'))(input)?;
    Ok((input, g))
}

fn disjunction(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = separated_list1(char('|'), sequence)(input)?;
    Ok((input, RegexAST::Disjunction(g)))
}

fn plus(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(sequence, char('+'))(input)?;
    Ok((input, RegexAST::Plus(Box::new(g))))
}

fn star(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(sequence, char('*'))(input)?;
    Ok((input, RegexAST::Star(Box::new(g))))
}

fn option(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(sequence, char('?'))(input)?;
    Ok((input, RegexAST::Option(Box::new(g))))
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_string() {
        assert_eq!(string("abc"), Ok(("", RegexAST::String("abc".to_string()))));
    }

    #[test]
    fn test_epsilon() {
        assert_eq!(epsilon(""), Ok(("", RegexAST::Epsilon)));
    }

    #[test]
    fn test_class() {
        assert_eq!(class("[abc]"), Ok(("", RegexAST::Class(vec!['a', 'b', 'c']))));
    }

    #[test]
    fn test_complement_class() {
        assert_eq!(complement_class("[^abc]"), Ok(("", RegexAST::ClassComplement(vec!['a', 'b', 'c']))))
    }
}