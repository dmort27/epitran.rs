use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, char as nom_char, line_ending, none_of, one_of, space0},
    combinator::{map_res, recognize, success, value},
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated},
};
use nom::{Err, IResult, Parser};
use std::char;

#[derive(Debug, PartialEq, Clone)]
pub enum RegexAST {
    Char(char),
    Group(Vec<RegexAST>),
    Option(Box<RegexAST>),
    Star(Box<RegexAST>),
    Plus(Box<RegexAST>),
    Disjunction(Vec<RegexAST>),
    Class(Vec<RegexAST>),
    ClassComplement(Vec<RegexAST>),
    Macro(String),
    Initial(Box<RegexAST>),
    Final(Box<RegexAST>),
    Epsilon,
    Boundary,
    LeftContext(Box<RegexAST>),
    RightContext(Box<RegexAST>),
    Source(Box<RegexAST>),
    Target(Box<RegexAST>),
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
    pub left: RegexAST,
    pub right: RegexAST,
    pub source: RegexAST,
    pub target: RegexAST,
}

type ParseError<'a> = Err<nom::error::Error<&'a str>>;

fn character(input: &str) -> IResult<&str, RegexAST> {
    let (input, c) = none_of(" />_()[]-|*+^#:%")(input)?;
    Ok((input, RegexAST::Char(c)))
}

fn uni_esc(input: &str) -> IResult<&str, RegexAST> {
    let mut parser = map_res(
        preceded(
            tag("\\u"),
            recognize(many1(one_of("0123456789abcdefABCDEF"))),
        ),
        |out: &str| u32::from_str_radix(out, 16),
    );

    let (input, num) = parser.parse(input)?;
    Ok((input, RegexAST::Char(std::char::from_u32(num).unwrap())))
}

fn escape(input: &str) -> IResult<&str, RegexAST> {
    let mut parser = preceded(tag("\\"), one_of("\\ /<>_()[]-|*+^#:%"));
    let (input, c) = parser.parse(input)?;
    Ok((input, RegexAST::Char(c)))
}

fn class(input: &str) -> IResult<&str, RegexAST> {
    let mut parser = delimited(
        nom_char('['),
        many1(alt((escape, uni_esc, character))),
        nom_char(']'),
    );
    let (input, s) = parser.parse(input)?;
    Ok((input, RegexAST::Class(s)))
}

fn complement_class(input: &str) -> IResult<&str, RegexAST> {
    let mut parser = delimited(
        nom_char('['),
        preceded(nom_char('^'), many1(alt((escape, uni_esc, character)))),
        nom_char(']'),
    );
    let (input, s) = parser.parse(input)?;
    Ok((input, RegexAST::ClassComplement(s)))
}

fn sequence(input: &str) -> IResult<&str, RegexAST> {
    let mut parser = many1(alt((
        mac,
        star,
        plus,
        option,
        disjunction,
        class,
        complement_class,
        group,
        word_initial,
        word_final,
        uni_esc,
        escape,
        character,
    )));
    let (input, g) = parser.parse(input)?;
    Ok((input, RegexAST::Group(g)))
}

fn group(input: &str) -> IResult<&str, RegexAST> {
    let mut parser = delimited(nom_char('('), sequence, nom_char(')'));
    let (input, g) = parser.parse(input)?;
    Ok((input, g))
}

fn characters(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = many1(character).parse(input)?;
    Ok((input, RegexAST::Group(g)))
}

fn regex(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((sequence, success(RegexAST::Epsilon))).parse(input)?;
    Ok((input, g))
}

fn left_context(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((
        sequence,
        value(RegexAST::Boundary, tag("#")),
        success(RegexAST::Epsilon),
    ))
    .parse(input)?;
    Ok((input, RegexAST::LeftContext(Box::new(g))))
}

fn right_context(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((
        sequence,
        value(RegexAST::Boundary, tag("#")),
        success(RegexAST::Epsilon),
    ))
    .parse(input)?;
    Ok((input, RegexAST::RightContext(Box::new(g))))
}

fn source(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((value(RegexAST::Epsilon, tag("0")), sequence)).parse(input)?;
    Ok((input, RegexAST::Source(Box::new(g))))
}

fn target(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((value(RegexAST::Epsilon, tag("0")), characters)).parse(input)?;
    Ok((input, RegexAST::Target(Box::new(g))))
}

fn disjunction(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = delimited(
        nom_char('('),
        separated_list1(nom_char('|'), sequence),
        nom_char(')'),
    )
    .parse(input)?;
    Ok((input, RegexAST::Disjunction(g)))
}

fn plus(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('+')).parse(input)?;
    Ok((input, RegexAST::Plus(Box::new(g))))
}

fn star(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('*')).parse(input)?;
    Ok((input, RegexAST::Star(Box::new(g))))
}

fn option(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('?')).parse(input)?;
    Ok((input, RegexAST::Option(Box::new(g))))
}

fn mac(input: &str) -> IResult<&str, RegexAST> {
    let (input, m) = delimited(tag("::"), alpha1, tag("::")).parse(input)?;
    Ok((input, RegexAST::Macro(m.to_string())))
}

fn boundary_sequence(input: &str) -> IResult<&str, RegexAST> {
    let (input, m) = alt((many1(character),)).parse(input)?;
    Ok((input, RegexAST::Group(m)))
}

fn word_initial(input: &str) -> IResult<&str, RegexAST> {
    let (input, m) = preceded(tag("#"), boundary_sequence).parse(input)?;
    Ok((input, RegexAST::Initial(Box::new(m))))
}

fn word_final(input: &str) -> IResult<&str, RegexAST> {
    let (input, m) = terminated(boundary_sequence, tag("#")).parse(input)?;
    Ok((input, RegexAST::Final(Box::new(m))))
}

fn comment(input: &str) -> IResult<&str, RegexAST> {
    value(
        RegexAST::Comment,
        pair(nom_char('%'), many0(none_of("\n\r"))),
    )
    .parse(input)
}

fn re_mac_def(input: &str) -> IResult<&str, (String, RegexAST)> {
    let (input, (_, name, _, _, _, re_group)) = (
        space0,
        delimited(tag("::"), alpha1, tag("::")),
        space0,
        tag("="),
        space0,
        regex,
    )
        .parse(input)?;
    Ok((input, (name.to_string(), re_group)))
}

pub fn rule(input: &str) -> IResult<&str, RewriteRule> {
    let (input, (source, _, target, _, left, _, right, _)) = (
        source,
        delimited(space0, tag("->"), space0),
        target,
        delimited(space0, tag("/"), space0),
        left_context,
        delimited(space0, tag("_"), space0),
        right_context,
        space0,
    )
        .parse(input)?;
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

pub fn rule_no_env(input: &str) -> IResult<&str, RewriteRule> {
    let (input, (source, _, target)) =
        (regex, delimited(space0, tag("->"), space0), regex).parse(input)?;
    Ok((
        input,
        RewriteRule {
            source,
            target,
            left: RegexAST::Epsilon,
            right: RegexAST::Epsilon,
        },
    ))
}

pub fn rule_with_comment(input: &str) -> IResult<&str, RewriteRule> {
    let (input, (source, _, target, _, left, _, right, _, _)) = (
        regex,
        delimited(space0, tag("->"), space0),
        regex,
        delimited(space0, tag("/"), space0),
        regex,
        delimited(space0, tag("_"), space0),
        regex,
        space0,
        comment,
    )
        .parse(input)?;
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

fn comment_statement(input: &str) -> IResult<&str, Statement> {
    value(Statement::Comment, comment).parse(input)
}

fn rule_statement(input: &str) -> IResult<&str, Statement> {
    let (input, r) = alt((rule, rule_no_env, rule_with_comment)).parse(input)?;
    Ok((input, Statement::Rule(r)))
}

fn macro_statement(input: &str) -> IResult<&str, Statement> {
    let (input, m) = re_mac_def(input)?;
    Ok((input, Statement::MacroDef(m)))
}

pub fn parse_script(input: &str) -> Result<Vec<Statement>, ParseError> {
    let mut parser = pair(
        separated_list0(
            many1(line_ending),
            alt((macro_statement, rule_statement, comment_statement)),
        ),
        many0(line_ending),
    );

    parser.parse(input).map(|(_, (statements, _))| statements)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_character() {
        assert_eq!(character("abc"), Ok(("bc", RegexAST::Char('a'))));
    }

    #[test]
    fn test_uni_esc() {
        assert_eq!(uni_esc(r#"\u014B"#), Ok(("", RegexAST::Char('ŋ'))));
    }

    #[test]
    fn test_class() {
        assert_eq!(
            class("[abc]"),
            Ok((
                "",
                RegexAST::Class(vec![
                    RegexAST::Char('a'),
                    RegexAST::Char('b'),
                    RegexAST::Char('c')
                ])
            ))
        );
    }

    #[test]
    fn test_complement_class() {
        assert_eq!(
            complement_class("[^abc]"),
            Ok((
                "",
                RegexAST::ClassComplement(vec![
                    RegexAST::Char('a'),
                    RegexAST::Char('b'),
                    RegexAST::Char('c')
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
                    RegexAST::Class(vec![
                        RegexAST::Char('d'),
                        RegexAST::Char('e'),
                        RegexAST::Char('f')
                    ])
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
            mac("::macro::"),
            Ok(("", RegexAST::Macro("macro".to_string())))
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
    fn test_rule_no_env() {
        debug_assert_eq!(
            rule_no_env("a -> b"),
            Ok((
                "",
                RewriteRule {
                    left: RegexAST::Epsilon,
                    right: RegexAST::Epsilon,
                    source: RegexAST::Group(vec![RegexAST::Char('a')]),
                    target: RegexAST::Group(vec![RegexAST::Char('b')]),
                }
            ))
        );
    }

    #[test]
    fn test_rule() {
        debug_assert_eq!(
            rule("a -> b / c _ d"),
            Ok((
                "",
                RewriteRule {
                    left: RegexAST::LeftContext(Box::new(RegexAST::Group(vec![RegexAST::Char(
                        'c'
                    )]))),
                    right: RegexAST::RightContext(Box::new(RegexAST::Group(vec![RegexAST::Char(
                        'd'
                    )]))),
                    source: RegexAST::Source(Box::new(RegexAST::Group(vec![RegexAST::Char('a')]))),
                    target: RegexAST::Target(Box::new(RegexAST::Group(vec![RegexAST::Char('b')]))),
                }
            ))
        );
    }

    #[test]
    fn test_rule2() {
        debug_assert_eq!(
            rule("b -> p / _ #"),
            Ok((
                "",
                RewriteRule {
                    left: RegexAST::LeftContext(Box::new(RegexAST::Epsilon)),
                    right: RegexAST::RightContext(Box::new(RegexAST::Boundary)),
                    source: RegexAST::Source(Box::new(RegexAST::Group(vec![RegexAST::Char('b')]))),
                    target: RegexAST::Target(Box::new(RegexAST::Group(vec![RegexAST::Char('p')]))),
                }
            ))
        )
    }

    #[test]
    fn test_rule3() {
        debug_assert_eq!(
            rule("0 -> 0 /  _ "),
            Ok((
                "",
                RewriteRule {
                    left: RegexAST::LeftContext(Box::new(RegexAST::Epsilon)),
                    right: RegexAST::RightContext(Box::new(RegexAST::Epsilon)),
                    source: RegexAST::Source(Box::new(RegexAST::Epsilon)),
                    target: RegexAST::Target(Box::new(RegexAST::Epsilon)),
                }
            ))
        )
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
}
