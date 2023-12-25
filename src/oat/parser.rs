// todo: return result
fn escape_string(s: &str) -> String {
    let mut out = String::new();
	let mut iter = s.chars();
    while let Some(c) = iter.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }

        let unescaped = iter.next().expect("escaped character");
        let escaped = match unescaped {
            'n' => '\n',
            't' => '\t',
            '\\' => '\\',
            '"' => '"',
            '\'' => '\'', // huh? why would we need to escape this?
            f@'0'..='9' => {
                let s = iter.next().expect("second escaped number");
                let t = iter.next().expect("third escaped number");
                if !matches!((s, t), ('0'..='9', '0'..='9')) {
                    panic!("must be numbers!");
                }
                let zero = '0' as u32;
                let n = (f as u32 - zero) * 100
                    + (s as u32 - zero) * 10
                    + (t as u32 - zero) ;
                if n > 255 {
                    panic!("illegal escaped character constant");
                }
                char::from_u32(n).unwrap()
            }
            c => panic!("unrecocgnized escape character: '{c}'"),
        };
        out.push(escaped);
    }
    out
}
