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
    let args = iter.map(ast_expr).collect::<Vec<_>>();
    Ast::Func { name, args }
}

fn ast_term0(term0: pest::iterators::Pair<Rule>) -> Ast {
    let t = term0.into_inner().next().unwrap();
    match t.as_rule() {
        Rule::func => ast_func(t),
        Rule::expr => {
            println!("{:?}", t);
            ast_expr(t)
        }
        Rule::int => Ast::Num(t.as_str().parse::<i64>().unwrap()),
        Rule::ident => Ast::Ident(t.as_str().to_owned()),
        _ => unreachable!(),
    }
}

fn ast_term1(term1: pest::iterators::Pair<Rule>) -> Ast {
    let mut iter = term1.into_inner();
    let first = iter.next().unwrap();
    if first.as_rule() == Rule::term0 {
        ast_term0(first)
    } else {
        let op = match first.as_rule() {
            Rule::plus => UniOp::Plus,
            Rule::neg => UniOp::Neg,
            _ => unreachable!(),
        };
        Ast::UniOp {
            op,
            expr: Box::new(ast_term0(iter.next().unwrap())),
        }
    }
}

fn binop(left: Ast, op: pest::iterators::Pair<Rule>, right: Ast) -> Ast {
    let op = match op.as_rule() {
        Rule::add => BinOp::Add,
        Rule::sub => BinOp::Sub,
        Rule::mul => BinOp::Mul,
        Rule::div => BinOp::Div,
        Rule::rem => BinOp::Rem,
        Rule::pow => BinOp::Pow,
        _ => unreachable!(),
    };
    Ast::BinOp {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn ast_expr(pair: pest::iterators::Pair<Rule>) -> Ast {
    use pest::prec_climber::{Assoc, Operator, PrecClimber};
    let climber = PrecClimber::new(vec![
        Operator::new(Rule::add, Assoc::Left) | Operator::new(Rule::sub, Assoc::Left),
        Operator::new(Rule::mul, Assoc::Left)
            | Operator::new(Rule::div, Assoc::Left)
            | Operator::new(Rule::rem, Assoc::Left),
        Operator::new(Rule::pow, Assoc::Right),
    ]);
    climber.climb(pair.into_inner(), ast_term1, binop)
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
