use nom::{
    character::complete::{char, none_of},
    combinator::{success},
    multi::{many1, separated_list1},
    sequence::{preceded, delimited, terminated},
    branch::alt,
    IResult,
    
};

#[derive(Debug, PartialEq)]
#[allow(dead_code)]
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
    Boundary,
}

#[derive(Debug, PartialEq)]
struct RewriteRule {
    left: RegexAST,
    right: RegexAST,
    source: RegexAST,
    target: String,
}

#[allow(dead_code)]
fn string(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = many1(none_of(" ()[]-|*+^#"))(input)?;
    Ok((input, RegexAST::String(s.into_iter().collect::<String>())))
}

#[allow(dead_code)]
fn class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(char('['), many1(none_of(" ()[]-|*+^#")), char(']'))(input)?;
    Ok((input, RegexAST::Class(s)))
}

#[allow(dead_code)]
fn complement_class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(char('['), preceded(char('^'), many1(none_of(" ()[]-|*+#"))), char(']'))(input)?;
    Ok((input, RegexAST::ClassComplement(s)))
}

#[allow(dead_code)]
fn epsilon(input: &str) -> IResult<&str, RegexAST> {
    let (input, _) = success("")(input)?;
    Ok((input, RegexAST::Epsilon))
}

#[allow(dead_code)]
fn sequence(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = many1(alt((string, class, complement_class, epsilon, disjunction, plus, star, option)))(input)?;
    Ok((input, RegexAST::Group(g)))
}

#[allow(dead_code)]
fn group(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = delimited(char('('), sequence, char(')'))(input)?;
    Ok((input, g))
}

#[allow(dead_code)]
fn disjunction(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = separated_list1(char('|'), sequence)(input)?;
    Ok((input, RegexAST::Disjunction(g)))
}

#[allow(dead_code)]
fn plus(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(sequence, char('+'))(input)?;
    Ok((input, RegexAST::Plus(Box::new(g))))
}

#[allow(dead_code)]
fn star(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(sequence, char('*'))(input)?;
    Ok((input, RegexAST::Star(Box::new(g))))
}

#[allow(dead_code)]
fn option(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(sequence, char('?'))(input)?;
    Ok((input, RegexAST::Option(Box::new(g))))
}

#[allow(dead_code)]
fn boundary(input: &str) -> IResult<&str, RegexAST> {
    let (input, _) = char('#')(input)?;
    Ok((input, RegexAST::Boundary))
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
        assert_eq!(complement_class("[^abc]"), Ok(("", RegexAST::ClassComplement(vec!['a', 'b', 'c']))));
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