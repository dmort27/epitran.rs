use parserule::langfst::build_lang_fst;
use parserule::rulefst::{apply_fst, rule_fst};
use parserule::ruleparse::{rule, RegexAST};
use rustfst::fst_impls::VectorFst;
use rustfst::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

fn evaluate_rule(symt: Arc<SymbolTable>, rule_str: &str, input: &str, output: &str) {
    let macros: &HashMap<String, RegexAST> = &HashMap::new();
    let (_, (rewrite_rule, _syms)) = rule(rule_str).expect("Failed to parse rule in test");
    let mut fst: VectorFst<TropicalWeight> =
        rule_fst(symt.clone(), macros, rewrite_rule).expect("Failed to create rule FST in test");
    // 1optimize_fst(&mut fst, 1e-5).expect("Could not optimize FST in test");
    assert_eq!(
        apply_fst(symt.clone(), fst, input.to_string()),
        output.to_string()
    )
}

const MAP: &str = r#"orth,phon
a,a
n,n,
g,g
l,l
ng,ŋ"#;

const MAP2: &str = r#"orth,phon
i,i
e,e
u,u
o,o
a,a
̂,ʔ
-,ʔ
',ʔ
m,m
p,p
b,b
n,n
t,t
d,d
s,s
l,l
r,ɾ
c,k
ch,t͡ʃ
ty,t͡ʃ
ts,t͡ʃ
j,d͡ʒ
dy,d͡ʒ
y,j
ng,ŋ
k,k
g,ɡ
w,w
h,h
"#;

const PRE: &str = r##"
::vowel:: = (a|e|i|o|u)

% Palatalization
di -> d͡ʒ / _ ::vowel::
ti -> t͡ʃ / _ ::vowel::
ni -> nʲ / _ ::vowel::
li -> lʲ / _ ::vowel::

% Devocalization
u -> w / _ ::vowel::
i -> j / _ ::vowel::
% u -> w / _ ::vowel::
"##;

const PRE2: &str = r##"
::vowel:: = (a|e|i|o|u)

% Devocalization

i -> j / _ ::vowel::
u -> w / _ ::vowel::


"##;

const POST: &str = r##"
"##;

fn test_build_realistic_lang_fst1() {
    let (symt, fst) = build_lang_fst(PRE, POST, MAP).expect("Failed to build language FST in test");
    let input = "#ngalngal#";
    assert_eq!(
        apply_fst(symt, fst, input.to_string()),
        "#ŋalŋal#".to_string()
    )
}

fn main() {
    test_build_realistic_lang_fst1();
}
