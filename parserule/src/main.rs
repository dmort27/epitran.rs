use parserule::langfst::build_lang_fst;
use parserule::rulefst::apply_fst;

const MAP: &str = r#"orth,phon
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

const POST: &str = r##"
"##;

fn test_build_realistic_lang_fst1() {
    let (symt, fst) = build_lang_fst(PRE.to_string(), POST.to_string(), MAP.to_string())
        .expect("Failed to build language FST in test");
    let pairs: Vec<(&str, &str)> = vec![
        ("#ngalngal#", "#ŋalŋal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
        ("#ngalngal#", "#ŋalɠal#"),
        ("#dino#", "#d͡ʒino#"),
        ("#iato#", "#jato#"),
        ("#lia#", "#lʲa#"),
        ("#tyatya#", "#t͡ʃat͡ʃa#"),
    ];
    for (itoken, otoken) in pairs {
        assert_eq!(
            apply_fst(symt.clone(), fst.clone(), itoken.to_string()),
            otoken.to_string()
        );
    }
}

fn main() {
    test_build_realistic_lang_fst1();
}
