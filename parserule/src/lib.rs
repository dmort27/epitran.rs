use nom::IResult;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, char as nom_char, line_ending, none_of, space0, space1},
    combinator::{success, value},
    multi::{many0, many1, separated_list1},
    sequence::{delimited, pair, preceded, terminated, tuple},
};

#[derive(Debug, PartialEq, Clone)]
#[allow(dead_code)]
pub enum RegexAST {
    Char(char),
    Group(Vec<RegexAST>),
    Option(Box<RegexAST>),
    Star(Box<RegexAST>),
    Plus(Box<RegexAST>),
    Disjunction(Vec<RegexAST>),
    Class(Vec<char>),
    ClassComplement(Vec<char>),
    Macro(String),
    MacroDef((String, Box<RegexAST>)),
    Epsilon,
    Boundary,
    Comment,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Comment,
    MacroDef((String, RegexAST)),
    Rule(RewriteRule),
}

#[derive(Debug, PartialEq, Clone)]
pub struct RewriteRule {
    left: RegexAST,
    right: RegexAST,
    source: RegexAST,
    target: RegexAST,
}

#[allow(dead_code)]
fn character(input: &str) -> IResult<&str, RegexAST> {
    let (input, c) = none_of(" ()[]-|*+^#%")(input)?;
    Ok((input, RegexAST::Char(c)))
}

#[allow(dead_code)]
fn class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) =
        delimited(nom_char('['), many1(none_of(" ()[]-|*+^#%")), nom_char(']'))(input)?;
    Ok((input, RegexAST::Class(s)))
}

#[allow(dead_code)]
fn complement_class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(
        nom_char('['),
        preceded(nom_char('^'), many1(none_of(" ()[]-|*+#%"))),
        nom_char(']'),
    )(input)?;
    Ok((input, RegexAST::ClassComplement(s)))
}

#[allow(dead_code)]
fn sequence(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = many1(alt((
        star,
        plus,
        option,
        disjunction,
        class,
        complement_class,
        group,
        mac,
        boundary,
        character,
    )))(input)?;
    Ok((input, RegexAST::Group(g)))
}

#[allow(dead_code)]
fn group(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = (delimited(nom_char('('), sequence, nom_char(')')))(input)?;
    Ok((input, g))
}

#[allow(dead_code)]
fn regex(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((sequence, success(RegexAST::Epsilon)))(input)?;
    Ok((input, g))
}

#[allow(dead_code)]
fn disjunction(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = delimited(
        nom_char('('),
        separated_list1(nom_char('|'), sequence),
        nom_char(')'),
    )(input)?;
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
fn mac(input: &str) -> IResult<&str, RegexAST> {
    let (input, m) = delimited(tag("::"), alpha1, tag("::"))(input)?;
    Ok((input, RegexAST::Macro(m.to_string())))
}

#[allow(dead_code)]
fn boundary(input: &str) -> IResult<&str, RegexAST> {
    let (input, _) = nom_char('#')(input)?;
    Ok((input, RegexAST::Boundary))
}

#[allow(dead_code)]
fn comment(input: &str) -> IResult<&str, RegexAST> {
    value(
        RegexAST::Comment,
        pair(nom_char('%'), many0(none_of("\n\r"))),
    )(input)
}

#[allow(dead_code)]
fn re_mac_def(input: &str) -> IResult<&str, (String, RegexAST)> {
    let (input, (_, name, _, _, _, re_group)) = tuple((
        space0,
        delimited(tag("::"), alpha1, tag("::")),
        space0,
        tag("="),
        space0,
        regex,
    ))(input)?;
    Ok((input, (name.to_string(), re_group)))
}

#[allow(dead_code)]
fn rule(input: &str) -> IResult<&str, RewriteRule> {
    let (input, (source, _, target, _, left, _, right)) = tuple((
        regex,
        delimited(space0, tag("->"), space0),
        regex,
        delimited(space0, tag("/"), space0),
        regex,
        delimited(space0, tag("_"), space0),
        regex,
    ))(input)?;
    Ok((
        input,
        RewriteRule {
            source,
            target,
            left,
            right,
        },
    ))
}

#[allow(dead_code)]
fn rule_with_comment(input: &str) -> IResult<&str, RewriteRule> {
    let (input, (source, _, target, _, left, _, right, _, _)) = tuple((
        regex,
        delimited(space0, tag("->"), space0),
        regex,
        delimited(space0, tag("/"), space0),
        regex,
        delimited(space0, tag("_"), space0),
        regex,
        space0,
        comment,
    ))(input)?;
    Ok((
        input,
        RewriteRule {
            left,
            right,
            source,
            target,
        },
    ))
}

#[allow(dead_code)]
fn comment_statment(input: &str) -> IResult<&str, Statement> {
    value(Statement::Comment, comment)(input)
}

#[allow(dead_code)]
fn rule_statement(input: &str) -> IResult<&str, Statement> {
    let (input, r) = alt((rule, rule_with_comment))(input)?;
    Ok((input, Statement::Rule(r)))
}

#[allow(dead_code)]
fn macro_statement(input: &str) -> IResult<&str, Statement> {
    let (input, m) = re_mac_def(input)?;
    Ok((input, Statement::MacroDef(m)))
}

#[allow(dead_code)]
pub fn parse_rule_file(input: &str) -> IResult<&str, Vec<Statement>> {
    let (input, (statements, _)) = pair(
        separated_list1(
            line_ending,
            alt((macro_statement, rule_statement, comment_statment)),
        ),
        many0(line_ending),
    )(input)?;
    Ok((input, statements))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_character() {
        assert_eq!(character("abc"), Ok(("bc", RegexAST::Char('a'))));
    }

    #[test]
    fn test_class() {
        assert_eq!(
            class("[abc]"),
            Ok(("", RegexAST::Class(vec!['a', 'b', 'c'])))
        );
    }

    #[test]
    fn test_complement_class() {
        assert_eq!(
            complement_class("[^abc]"),
            Ok(("", RegexAST::ClassComplement(vec!['a', 'b', 'c'])))
        );
    }

    #[test]
    fn test_sequence3() {
        debug_assert_eq!(
            sequence("a[123]#"),
            Ok((
                "",
                RegexAST::Group(vec![
                    RegexAST::Char('a'),
                    RegexAST::Class(vec!['1', '2', '3']),
                    RegexAST::Boundary
                ])
            ))
        );
    }

    #[test]
    fn test_sequence4() {
        debug_assert_eq!(
            sequence("a"),
            Ok(("", RegexAST::Group(vec![RegexAST::Char('a')])))
        );
    }

    #[test]
    fn test_group3() {
        debug_assert_eq!(
            group("(a)"),
            Ok(("", RegexAST::Group(vec![RegexAST::Char('a')])))
        );
    }

    #[test]
    fn test_group2() {
        debug_assert_eq!(
            group("(a[def])"),
            Ok((
                "",
                RegexAST::Group(vec![
                    RegexAST::Char('a'),
                    RegexAST::Class(vec!['d', 'e', 'f'])
                ])
            ))
        );
    }

    #[test]
    fn test_regex1() {
        debug_assert_eq!(
            regex("a"),
            Ok(("", RegexAST::Group(vec![RegexAST::Char('a')])))
        );
    }

    #[test]
    fn test_regex2() {
        debug_assert_eq!(regex(""), Ok(("", RegexAST::Epsilon)));
    }

    #[test]
    fn test_plus() {
        debug_assert_eq!(
            plus("a+"),
            Ok(("", RegexAST::Plus(Box::new(RegexAST::Char('a')))))
        )
    }

    #[test]
    fn test_regex_with_plus1() {
        debug_assert_eq!(
            regex("a+b"),
            Ok((
                "",
                RegexAST::Group(vec![
                    RegexAST::Plus(Box::new(RegexAST::Char('a'))),
                    RegexAST::Char('b'),
                ])
            ))
        );
    }

    #[test]
    fn test_mac() {
        debug_assert_eq!(
            regex("::macro::"),
            Ok((
                "",
                RegexAST::Group(vec![RegexAST::Macro("macro".to_string())])
            ))
        );
    }

    #[test]
    fn test_re_mac_def() {
        debug_assert_eq!(
            re_mac_def("::abc:: = (d|e)"),
            Ok((
                "",
                (
                    "abc".to_string(),
                    RegexAST::Group(vec![RegexAST::Disjunction(vec![
                        RegexAST::Group(vec!(RegexAST::Char('d'))),
                        RegexAST::Group(vec!(RegexAST::Char('e'))),
                    ])])
                )
            ))
        );
    }

    #[test]
    fn test_comment() {
        debug_assert_eq!(comment("% Comment"), Ok(("", RegexAST::Comment,)))
    }

    #[test]
    fn test_rule() {
        debug_assert_eq!(
            rule("a -> b / c _ d"),
            Ok((
                "",
                RewriteRule {
                    left: RegexAST::Group(vec![RegexAST::Char('c')]),
                    right: RegexAST::Group(vec![RegexAST::Char('d')]),
                    source: RegexAST::Group(vec![RegexAST::Char('a')]),
                    target: RegexAST::Group(vec![RegexAST::Char('b')]),
                }
            ))
        );
    }

    #[test]
    fn test_rule_with_comment() {
        debug_assert_eq!(
            rule_with_comment("a -> b / c _ d % Comment"),
            Ok((
                "",
                RewriteRule {
                    left: RegexAST::Group(vec![RegexAST::Char('c')]),
                    right: RegexAST::Group(vec![RegexAST::Char('d')]),
                    source: RegexAST::Group(vec![RegexAST::Char('a')]),
                    target: RegexAST::Group(vec![RegexAST::Char('b')]),
                }
            ))
        );
    }

    #[test]
    fn test_sep_list() {
        fn sep(input: &str) -> IResult<&str, Vec<&str>> {
            separated_list1(nom_char('\n'), alpha1)(input)
        }
        debug_assert_eq!(sep("abc\ndef\n"), Ok(("", vec!["abc", "def"])))
    }
}
