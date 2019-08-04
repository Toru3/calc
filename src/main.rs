use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "calc.pest"]
pub struct ExprParser;

#[derive(Debug, Clone, PartialEq, Eq)]
enum UniOp {
    Plus,
    Neg,
}

impl std::fmt::Display for UniOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UniOp::Plus => write!(f, "+"),
            UniOp::Neg => write!(f, "-"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
            BinOp::Pow => write!(f, "^"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Ast {
    Num(i64),
    Ident(String),
    BinOp {
        op: BinOp,
        left: Box<Ast>,
        right: Box<Ast>,
    },
    UniOp {
        op: UniOp,
        expr: Box<Ast>,
    },
    Func {
        name: String,
        args: Vec<Ast>,
    },
    //Dummy,
}

impl std::fmt::Display for Ast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ast::Num(n) => write!(f, "{}", n),
            Ast::Ident(s) => write!(f, "{}", s),
            Ast::BinOp { op, left, right } => write!(f, "({} {} {})", op, left, right),
            Ast::UniOp { op, expr } => write!(f, "({} {})", op, expr),
            Ast::Func { name, args } => {
                write!(f, "(")?;
                write!(f, "{}", name)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
            //Ast::Dummy => write!(f, "X"),
        }
    }
}

fn ast_func(func: pest::iterators::Pair<Rule>) -> Ast {
    let mut iter = func.into_inner();
    let func_name = iter.next().unwrap();
    assert_eq!(func_name.as_rule(), Rule::ident);
    let name = func_name.as_str().to_owned();
    let args = iter.next().unwrap();
    assert_eq!(args.as_rule(), Rule::args);
    let args = args.into_inner().map(ast_expr).collect::<Vec<_>>();
    Ast::Func { name, args }
}

fn ast_atom(atom: pest::iterators::Pair<Rule>) -> Ast {
    let t = atom.into_inner().next().unwrap();
    match t.as_rule() {
        Rule::int => Ast::Num(t.as_str().parse::<i64>().unwrap()),
        Rule::ident => Ast::Ident(t.as_str().to_owned()),
        _ => unreachable!(),
    }
}

fn ast_term0(term0: pest::iterators::Pair<Rule>) -> Ast {
    let t = term0.into_inner().next().unwrap();
    match t.as_rule() {
        Rule::func => ast_func(t),
        Rule::expr => {
            println!("{:?}", t);
            ast_expr(t)
        }
        Rule::atom => ast_atom(t),
        _ => unreachable!(),
    }
}

fn ast_term1(term1: pest::iterators::Pair<Rule>) -> Ast {
    let mut iter = term1.into_inner();
    let first = iter.next().unwrap();
    if first.as_rule() == Rule::uniop {
        let op = match first.as_str() {
            "+" => UniOp::Plus,
            "-" => UniOp::Neg,
            _ => unreachable!(),
        };
        let second = iter.next().unwrap();
        let expr = Box::new(ast_term0(second));
        Ast::UniOp { op, expr }
    } else {
        assert_eq!(first.as_rule(), Rule::term0);
        ast_term0(first)
    }
}

fn ast_term2(term2: pest::iterators::Pair<Rule>) -> Ast {
    let mut iter = term2.into_inner();
    let first = iter.next().unwrap();
    assert_eq!(first.as_rule(), Rule::term1);
    let mut ast = ast_term1(first);
    if let Some(op) = iter.next() {
        assert_eq!(op.as_rule(), Rule::pow);
        let op = match op.as_str() {
            "^" => BinOp::Pow,
            _ => unreachable!(),
        };
        let right = iter.next().unwrap();
        assert_eq!(right.as_rule(), Rule::term2);
        let right = Box::new(ast_term2(right));
        ast = Ast::BinOp {
            op,
            left: Box::new(ast),
            right,
        };
    }
    dbg!(ast)
}

fn ast_term3(term3: pest::iterators::Pair<Rule>) -> Ast {
    let mut iter = term3.into_inner();
    let first = iter.next().unwrap();
    assert_eq!(first.as_rule(), Rule::term2);
    let mut ast = ast_term2(first);
    while let Some(op) = iter.next() {
        assert_eq!(op.as_rule(), Rule::mul);
        let op = match op.as_str() {
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Rem,
            _ => unreachable!(),
        };
        let right = iter.next().unwrap();
        assert_eq!(right.as_rule(), Rule::term2);
        let right = Box::new(ast_term2(right));
        ast = Ast::BinOp {
            op,
            left: Box::new(ast),
            right,
        };
    }
    dbg!(ast)
}

fn ast_expr(expr: pest::iterators::Pair<Rule>) -> Ast {
    let mut iter = expr.into_inner();
    let first = iter.next().unwrap();
    assert_eq!(first.as_rule(), Rule::term3);
    let mut ast = ast_term3(first);
    while let Some(op) = iter.next() {
        assert_eq!(op.as_rule(), Rule::add);
        let op = match op.as_str() {
            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            _ => unreachable!(),
        };
        let right = iter.next().unwrap();
        assert_eq!(right.as_rule(), Rule::term3);
        let right = Box::new(ast_term3(right));
        ast = Ast::BinOp {
            op,
            left: Box::new(ast),
            right,
        };
    }
    dbg!(ast)
}

fn make_ast(parsed: pest::iterators::Pairs<Rule>) -> Vec<Ast> {
    let mut v = Vec::new();
    for i in parsed {
        println!("{}", i);
        let a = match i.as_rule() {
            Rule::expr => ast_expr(i),
            _ => unreachable!(),
        };
        println!("{}", a);
        v.push(a);
    }
    v
}

fn prompt(s: &str) -> std::io::Result<()> {
    use std::io::{stdout, Write};
    let stdout = stdout();
    let mut stdout = stdout.lock();
    stdout.write_all(s.as_bytes())?;
    stdout.flush()
}

fn main() {
    use std::io::{stdin, BufRead, BufReader};
    let stdin = stdin();
    let stdin = stdin.lock();
    let stdin = BufReader::new(stdin);
    let mut lines = stdin.lines();
    loop {
        prompt("> ").unwrap();
        if let Some(Ok(line)) = lines.next() {
            let parsed = ExprParser::parse(Rule::expr, &line).unwrap();
            println!("{}", parsed);
            let _ast = make_ast(parsed);
        } else {
            break;
        }
    }
}
