use nom::IResult;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, char as nom_char, line_ending, none_of, one_of, space0},
    combinator::{map_res, recognize, success, value},
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated, tuple},
};
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
    pub left: RegexAST,
    pub right: RegexAST,
    pub source: RegexAST,
    pub target: RegexAST,
}

fn character(input: &str) -> IResult<&str, RegexAST> {
    let (input, c) = none_of(" />_()[]-|*+^#%")(input)?;
    Ok((input, RegexAST::Char(c)))
}

fn uni_esc(input: &str) -> IResult<&str, RegexAST> {
    let (input, num) = map_res(
    preceded(
        tag("\\u"),
        recognize(many1(one_of("0123456789abcdefABCDEF"))),
    ),
    |out: &str| u32::from_str_radix(out, 16)
    )(input)?;
    Ok((input, RegexAST::Char(std::char::from_u32(num).unwrap())))
}

fn escape(input: &str) -> IResult<&str, RegexAST> {
    let (input, c) = preceded(tag("\\"), one_of("\\ /<>_()[]-|*+^#%"))(input)?;
    Ok((input, RegexAST::Char(c)))
}

fn class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(
        nom_char('['),
        many1(alt((escape, uni_esc, character))),
        nom_char(']'),
    )(input)?;
    Ok((input, RegexAST::Class(s)))
}

fn complement_class(input: &str) -> IResult<&str, RegexAST> {
    let (input, s) = delimited(
        nom_char('['),
        preceded(nom_char('^'), many1(alt((escape, uni_esc, character)))),
        nom_char(']'),
    )(input)?;
    Ok((input, RegexAST::ClassComplement(s)))
}

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
        uni_esc,
        escape,
        character,
    )))(input)?;
    Ok((input, RegexAST::Group(g)))
}

fn group(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = (delimited(nom_char('('), sequence, nom_char(')')))(input)?;
    Ok((input, g))
}

fn regex(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = alt((sequence, success(RegexAST::Epsilon)))(input)?;
    Ok((input, g))
}

fn disjunction(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = delimited(
        nom_char('('),
        separated_list1(nom_char('|'), sequence),
        nom_char(')'),
    )(input)?;
    Ok((input, RegexAST::Disjunction(g)))
}

fn plus(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('+'))(input)?;
    Ok((input, RegexAST::Plus(Box::new(g))))
}

fn star(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('*'))(input)?;
    Ok((input, RegexAST::Star(Box::new(g))))
}

fn option(input: &str) -> IResult<&str, RegexAST> {
    let (input, g) = terminated(alt((group, character)), nom_char('?'))(input)?;
    Ok((input, RegexAST::Option(Box::new(g))))
}

fn mac(input: &str) -> IResult<&str, RegexAST> {
    let (input, m) = delimited(tag("::"), alpha1, tag("::"))(input)?;
    Ok((input, RegexAST::Macro(m.to_string())))
}

fn boundary(input: &str) -> IResult<&str, RegexAST> {
    let (input, _) = tag("#")(input)?;
    Ok((input, RegexAST::Boundary))
}

fn comment(input: &str) -> IResult<&str, RegexAST> {
    value(
        RegexAST::Comment,
        pair(nom_char('%'), many0(none_of("\n\r"))),
    )(input)
}

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

fn rule(input: &str) -> IResult<&str, RewriteRule> {
    let (input, (source, _, target, _, left, _, right, _)) = tuple((
        regex,
        delimited(space0, tag("->"), space0),
        regex,
        delimited(space0, tag("/"), space0),
        regex,
        delimited(space0, tag("_"), space0),
        regex,
        space0,
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

fn rule_no_env(input: &str) -> IResult<&str, RewriteRule> {
    let (input, (source, _, target)) =
        tuple((regex, delimited(space0, tag("->"), space0), regex))(input)?;
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

fn comment_statment(input: &str) -> IResult<&str, Statement> {
    value(Statement::Comment, comment)(input)
}

fn rule_statement(input: &str) -> IResult<&str, Statement> {
    let (input, r) = alt((rule, rule_with_comment))(input)?;
    Ok((input, Statement::Rule(r)))
}

fn macro_statement(input: &str) -> IResult<&str, Statement> {
    let (input, m) = re_mac_def(input)?;
    Ok((input, Statement::MacroDef(m)))
}
/// Given an a pre-processing or post-processing script, return a vector of
/// parsed statements that can be converted to a weighted finite state
/// transducer.
///
/// ```rust
/// use parserule::*;
///
/// let script = "b -> p / _ #\n";
/// let parsed = parse_script(script);
/// assert_eq!(
///     parsed, vec![
///         Statement::Rule(
///             RewriteRule{
///                 left: RegexAST::Group(vec![RegexAST::Epsilon]),
///                 right: RegexAST::Group(vec![RegexAST::Boundary]),
///                 source: RegexAST::Group(vec![RegexAST::Char('b')]),
///                 target: RegexAST::Group(vec![RegexAST::Char('p')])
///             }
///         )
///     ]
/// )
/// ```
pub fn parse_script(input: &str) -> Vec<Statement> {
    let (_, (statements, _)) = pair(
        separated_list0(
            line_ending,
            alt((macro_statement, rule_statement, comment_statment)),
        ),
        many0(line_ending),
    )(input)
    .unwrap();
    statements
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
    fn test_sequence3() {
        debug_assert_eq!(
            sequence("a[123]#"),
            Ok((
                "",
                RegexAST::Group(vec![
                    RegexAST::Char('a'),
                    RegexAST::Class(vec![
                        RegexAST::Char('1'),
                        RegexAST::Char('2'),
                        RegexAST::Char('3')
                    ]),
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
                    left: RegexAST::Group(vec![RegexAST::Char('c')]),
                    right: RegexAST::Group(vec![RegexAST::Char('d')]),
                    source: RegexAST::Group(vec![RegexAST::Char('a')]),
                    target: RegexAST::Group(vec![RegexAST::Char('b')]),
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
                    left: RegexAST::Epsilon,
                    right: RegexAST::Group(vec![RegexAST::Boundary]),
                    source: RegexAST::Group(vec![RegexAST::Char('b')]),
                    target: RegexAST::Group(vec![RegexAST::Char('p')]),
                }
            ))
        )
    }

    #[test]
    fn test_rule3() {
        debug_assert_eq!(
            rule(" ->  /  _ "),
            Ok((
                "",
                RewriteRule {
                    left: RegexAST::Epsilon,
                    right: RegexAST::Epsilon,
                    source: RegexAST::Epsilon,
                    target: RegexAST::Epsilon,
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
