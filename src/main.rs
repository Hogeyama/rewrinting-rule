#![allow(unused_imports)]
#![allow(dead_code)]

extern crate combine;
extern crate combine_language;
use combine::parser::char::{char, digit, letter};
use combine::parser::item;
use combine::stream::state::State;
use combine::*;
use std::collections::HashMap;
use std::io::Read;

mod types {
    use std::collections::HashMap;

    #[derive(Debug, Clone)]
    pub struct Prog {
        main: Head,
        rules: HashMap<Head, Rule>,
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Head {
        name: String,
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Rule {
        head: Head,
        args: Vec<Var>,
        reduce: Vec<(Cond, Term)>,
    }

    type Cond = Term;

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Term {
        Unit,
        End,
        Bottom,
        Fail,
        Var(Var),
        Bool(bool),
        Int(i64),
        //
        App(Box<Term>, Box<Term>),
        Ope(BinOp, Box<Term>, Box<Term>),
        Neg(Box<Term>),
        Not(Box<Term>),
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub enum BinOp {
        Add,
        Sub,
        And,
        Or,
        Equal,
        Lt,
        Le,
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Var {
        pub name: String,
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Trace(Vec<(Head, i32)>);
}

mod parser {
    use combine::char::*;
    use combine::char::{char, string};
    use combine::combinator::*;
    use combine::parser::char::{digit, letter};
    use combine::parser::*;
    use combine::stream::state::State;
    use combine::*;
    use combine_language::*;
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::io::Read;
    use std::marker::PhantomData;

    use types::*;

    // Trick!
    // https://stackoverflow.com/questions/50547766/how-can-i-get-impl-trait-to-use-the-appropriate-lifetime-for-a-mutable-reference
    trait Captures<'a> {}
    impl<'a, T: ?Sized> Captures<'a> for T {}

    fn language_env<'a, I>() -> LanguageEnv<'a, I>
    where
        I: Stream<Item = char> + 'a,
        I::Error: ParseError<I::Item, I::Range, I::Position>,
    {
        LanguageEnv::new(LanguageDef {
            ident: Identifier {
                start: letter(),
                rest: alpha_num(),
                reserved: ["when", "true", "false", "not", "end", "fail"]
                    .iter()
                    .map(|x| (*x).into())
                    .collect(),
            },
            op: Identifier {
                start: satisfy(|c| "+-&|=<".chars().any(|x| x == c)),
                rest: satisfy(|c| "+-&|=<".chars().any(|x| x == c)),
                reserved: ["+", "-", "&&", "||", "=", "<", "<="]
                    .iter()
                    .map(|x| (*x).into())
                    .collect(),
            },
            comment_start: string("/*").map(|_| ()),
            comment_end: string("*/").map(|_| ()),
            comment_line: string("//").map(|_| ()),
        })
    }

    struct MyParser<'a, I>
    where
        I: Stream<Item = char> + 'a,
        I::Error: ParseError<I::Item, I::Range, I::Position>,
    {
        env: LanguageEnv<'a, I>,
    }

    impl<'a, I> MyParser<'a, I>
    where
        I: Stream<Item = char> + 'a,
        I::Error: ParseError<I::Item, I::Range, I::Position>,
    {
        fn hoge<'b>(&'b self) -> Map<Value<I, i64>, impl FnMut(i64) -> Term> {
            value(120i64).map(Term::Int)
        }

        fn new() -> Self {
            MyParser {
                env: language_env(),
            }
        }

        fn term<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            let op_parser = choice!(
                self.env.reserved_op("||"),
                self.env.reserved_op("&&"),
                self.env.reserved_op("<"),
                self.env.reserved_op("<="),
                self.env.reserved_op("="),
                self.env.reserved_op("-"),
                self.env.reserved_op("+")
            )
            .map(|op_s| {
                let (op, prec) = match op_s {
                    "||" => (BinOp::Or, 2),
                    "&&" => (BinOp::And, 3),
                    "=" => (BinOp::Equal, 4),
                    "<" => (BinOp::Lt, 4),
                    "<=" => (BinOp::Le, 4),
                    "-" => (BinOp::Sub, 6),
                    "+" => (BinOp::Add, 6),
                    _ => unreachable!(),
                };
                (
                    op,
                    Assoc {
                        precedence: prec,
                        fixity: Fixity::Left,
                    },
                )
            });
            expression_parser(self.aterm(), op_parser, |t1, op, t2| {
                Term::Ope(op, Box::new(t1), Box::new(t2))
            })
        }
        fn aterm<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            let not_t = self
                .env
                .reserved("not")
                .with(self.atom().then(|a| value(Term::Not(Box::new(a)))));
            let app_t = combine::many1::<Vec<_>, _>(self.atom()).map(|ts| {
                let mut iter = ts.into_iter();
                let x = iter.next().unwrap();
                let t = iter.fold(x, |t1, t2| Term::App(Box::new(t1), Box::new(t2)));
                t
            });
            choice!(not_t, app_t)
        }

        fn atom<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            choice!(
                self.bottom(),
                self.unit(),
                self.fail(),
                self.end(),
                self.int(),
                self.var().map(|v| Term::Var(v)),
                self.bool(),
                opaque(move |f| f(&mut self.env.parens(self.term()))) // マクロ使ってよいなら opaque!(&mut self.env.parens(self.term()))
            )
        }

        fn int<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            self.env.integer().map(|n| Term::Int(n))
        }

        fn var<'b>(&'b self) -> impl Parser<Input = I, Output = Var> + Captures<'a> + 'b {
            combine::attempt(self.env.identifier()).then(|x| value(Var { name: x }))
        }

        fn bottom<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            self.env.reserved("_|_").with(value(Term::Bottom))
        }

        fn unit<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            self.env.reserved("()").with(value(Term::Unit))
        }

        fn end<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            self.env.reserved("end").with(value(Term::End))
        }

        fn fail<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            self.env.symbol("{fail}").with(value(Term::Fail))
        }

        fn bool<'b>(&'b self) -> impl Parser<Input = I, Output = Term> + Captures<'a> + 'b {
            self.raw_bool().map(|b| Term::Bool(b))
        }
        fn raw_bool<'b>(&'b self) -> impl Parser<Input = I, Output = bool> + Captures<'a> + 'b {
            choice!(
                self.env.symbol("true").with(value(true)),
                self.env.symbol("false").with(value(false))
            )
        }
    }

    pub fn main() -> std::io::Result<()> {
        // let mut buffer = String::new();
        // std::io::stdin().read_to_string(&mut buffer)?;
        // let input = buffer.as_str();
        let input = "1 <= x || true && (f false)";

        let p = MyParser::new();
        let x = p.term().easy_parse(input);
        println!("{:?}", x);
        Ok(())
    }
}

fn main() {
    let _x = parser::main();
}
