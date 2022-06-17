use nom::IResult;
use nom::{
    character::complete::{char as nom_char, none_of},
    combinator::{success},
    multi::{many1, separated_list1},
    sequence::{preceded, delimited, terminated},
    branch::alt,
};

#[derive(Debug, PartialEq, Clone)]
#[allow(dead_code)]
enum RegexAST {
    Char(char),
    Group(Vec<RegexAST>),
    Option(Box<RegexAST>),
    Star(Box<RegexAST>),
    Plus(Box<RegexAST>),
    Disjunction(Vec<RegexAST>),
    Class(Vec<char>),
    ClassComplement(Vec<char>),
    Epsilon,
    Boundary,
}

#[derive(Debug, PartialEq)]
struct RewriteRule {
    left: RegexAST,
    right: RegexAST,
    source: RegexAST,
    target: RegexAST,
}

#[allow(dead_code)]
fn character(input: &str) -> IResult<&str, RegexAST> {
    let (input, c) = none_of(" ()[]-|*+^#")(input)?;
    Ok((input, RegexAST::Char(c)))
}

#[allow(dead_code)]
fn class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(nom_char('['), many1(none_of(" ()[]-|*+^#")), nom_char(']'))(input)?;
    Ok((input, RegexAST::Class(s)))
}

#[allow(dead_code)]
fn complement_class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(nom_char('['), preceded(nom_char('^'), many1(none_of(" ()[]-|*+#"))), nom_char(']'))(input)?;
    Ok((input, RegexAST::ClassComplement(s)))
}

#[allow(dead_code)]
fn epsilon(input: &str) -> IResult<&str, RegexAST> {
    success(RegexAST::Epsilon)(input)
}

#[allow(dead_code)]
fn sequence(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = many1(alt((character, class, complement_class, boundary, group)))(input)?;
    Ok((input, RegexAST::Group(g)))
}

#[allow(dead_code)]
fn group(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((delimited(nom_char('('), sequence, nom_char(')')), epsilon))(input)?;
    Ok((input, g))
}

#[allow(dead_code)]
fn disjunction(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = separated_list1(nom_char('|'), sequence)(input)?;
    Ok((input, RegexAST::Disjunction(g)))
}

#[allow(dead_code)]
fn plus(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('+'))(input)?;
    Ok((input, RegexAST::Plus(Box::new(g))))
}

#[allow(dead_code)]
fn star(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('*'))(input)?;
    Ok((input, RegexAST::Star(Box::new(g))))
}

#[allow(dead_code)]
fn option(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('?'))(input)?;
    Ok((input, RegexAST::Option(Box::new(g))))
}

#[allow(dead_code)]
fn boundary(input: &str) -> IResult<&str, RegexAST> {
    let (input, _) = nom_char('#')(input)?;
    Ok((input, RegexAST::Boundary))
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_character() {
        assert_eq!(character("abc"), Ok(("bc", RegexAST::Char('a'))));
    }

    #[test]
    fn test_epsilon() {
        assert_eq!(epsilon("abc"), Ok(("abc", RegexAST::Epsilon)));
    }

    #[test]
    fn test_class() {
        assert_eq!(class("[abc]"), Ok(("", RegexAST::Class(vec!['a', 'b', 'c']))));
    }

    #[test]
    fn test_complement_class() {
        assert_eq!(complement_class("[^abc]"), Ok(("", RegexAST::ClassComplement(vec!['a', 'b', 'c']))));
    }

    #[test]
    fn test_sequence3() {
        debug_assert_eq!(sequence("a[123]#"), Ok(("", RegexAST::Group(vec![RegexAST::Char('a'), RegexAST::Class(vec!['1', '2', '3']), RegexAST::Boundary]))));
    }

    #[test]
    fn test_group1() {
        debug_assert_eq!(group(""), Ok(("", RegexAST::Epsilon)));
    }

    #[test]
    fn test_group3() {
        debug_assert_eq!(group("(a)"), Ok(("", RegexAST::Group(vec![RegexAST::Char('a')]))));
    }

    #[test]
    fn test_group2() {
        debug_assert_eq!(group("(a[def])"), Ok(("", RegexAST::Group(vec![RegexAST::Char('a'), RegexAST::Class(vec!['d', 'e', 'f'])]))));
    }

    // #[test]
    // fn test_group() {
    //     debug_assert_eq!(sequence("abc[def]"), Ok(("", RegexAST::Group(vec![RegexAST::String("abc".to_string()), RegexAST::Class(vec!['d', 'e', 'f'])]))));
    // }

    // #[test]
    // fn test_sequence_2() {
    //     debug_assert_eq!(sequence("abc"), Ok(("", RegexAST::Group(vec![RegexAST::String("abc".to_string())]))));
    // }
}