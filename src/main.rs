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

macro_rules! binop_helper {
    ($func_name:ident, $name:ident) => {
        fn $func_name(left: Ast, right: Ast) -> Self {
            Ast::BinOp {
                op: BinOp::$name,
                left: Box::new(left),
                right: Box::new(right),
            }
        }
    };
}
macro_rules! uniop_helper {
    ($func_name:ident, $name:ident) => {
        fn $func_name(expr: Ast) -> Self {
            Ast::UniOp {
                op: UniOp::$name,
                expr: Box::new(expr),
            }
        }
    };
}

impl Ast {
    binop_helper!(add, Add);
    binop_helper!(sub, Sub);
    binop_helper!(mul, Mul);
    binop_helper!(div, Div);
    //binop_helper!(rem, Rem);
    binop_helper!(pow, Pow);
    //uniop_helper!(plus, Plus);
    uniop_helper!(neg, Neg);
    fn func(name: String, args: Vec<Ast>) -> Self {
        Ast::Func { name, args }
    }
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

fn eval(a: Ast) -> Result<f64, String> {
    let r = match a {
        Ast::Num(n) => n as f64,
        Ast::Ident(name) => return Err(format!("undefined variable: {}", name)),
        Ast::BinOp { op, left, right } => match op {
            BinOp::Add => eval(*left)? + eval(*right)?,
            BinOp::Sub => eval(*left)? - eval(*right)?,
            BinOp::Mul => eval(*left)? * eval(*right)?,
            BinOp::Div => eval(*left)? / eval(*right)?,
            BinOp::Rem => unimplemented!(),
            BinOp::Pow => eval(*left)?.powf(eval(*right)?),
        },
        Ast::UniOp { op, expr } => match op {
            UniOp::Plus => eval(*expr)?,
            UniOp::Neg => -eval(*expr)?,
        },
        Ast::Func { name, args } => {
            let args = args.into_iter().map(eval).collect::<Result<Vec<_>, _>>()?;
            match name.as_str() {
                "sin" => args[0].sin(),
                "cos" => args[0].cos(),
                "exp" => args[0].exp(),
                "log" => args[0].ln(),
                _ => return Err(format!("unknown function: {}", name)),
            }
        }
    };
    Ok(r)
}

fn have(a: &Ast, v: &str) -> bool {
    match a {
        Ast::Num(_) => false,
        Ast::Ident(x) => x == v,
        Ast::BinOp { left, right, .. } => have(left, v) || have(right, v),
        Ast::UniOp { expr, .. } => have(expr, v),
        Ast::Func { args, .. } => args.iter().any(|ast| have(ast, v)),
    }
}

fn diff_add(left: &Ast, right: &Ast, v: &str) -> Ast {
    match (have(left, v), have(right, v)) {
        (true, true) => Ast::add(derivative(left, v), derivative(right, v)),
        (true, false) => derivative(left, v),
        (false, true) => derivative(right, v),
        (false, false) => Ast::Num(0),
    }
}

fn diff_sub(left: &Ast, right: &Ast, v: &str) -> Ast {
    match (have(left, v), have(right, v)) {
        (true, true) => Ast::sub(derivative(left, v), derivative(right, v)),
        (true, false) => derivative(left, v),
        (false, true) => Ast::neg(derivative(right, v)),
        (false, false) => Ast::Num(0),
    }
}

fn diff_mul(left: &Ast, right: &Ast, v: &str) -> Ast {
    match (have(left, v), have(right, v)) {
        (true, true) => Ast::add(
            Ast::mul(derivative(left, v), right.clone()),
            Ast::mul(left.clone(), derivative(right, v)),
        ),
        (true, false) => Ast::mul(derivative(left, v), right.clone()),
        (false, true) => Ast::mul(left.clone(), derivative(right, v)),
        (false, false) => Ast::Num(0),
    }
}

fn diff_div(left: &Ast, right: &Ast, v: &str) -> Ast {
    match (have(left, v), have(right, v)) {
        (true, true) => Ast::sub(
            Ast::div(derivative(left, v), right.clone()),
            Ast::div(
                Ast::mul(left.clone(), derivative(right, v)),
                Ast::pow(right.clone(), Ast::Num(2)),
            ),
        ),
        (true, false) => Ast::div(derivative(left, v), right.clone()),
        (false, true) => Ast::neg(Ast::div(
            Ast::mul(left.clone(), right.clone()),
            Ast::pow(right.clone(), Ast::Num(2)),
        )),
        (false, false) => Ast::Num(0),
    }
}

fn diff_pow(left: &Ast, right: &Ast, v: &str) -> Ast {
    match (have(left, v), have(right, v)) {
        (true, true) => Ast::mul(
            Ast::pow(left.clone(), right.clone()),
            Ast::add(
                Ast::mul(
                    derivative(right, v),
                    Ast::func("log".to_string(), vec![left.clone()]),
                ),
                Ast::mul(right.clone(), Ast::div(derivative(left, v), left.clone())),
            ),
        ),
        (true, false) => Ast::mul(
            right.clone(),
            Ast::mul(
                derivative(left, v),
                Ast::pow(left.clone(), Ast::sub(right.clone(), Ast::Num(1))),
            ),
        ),
        (false, true) => Ast::mul(
            Ast::pow(left.clone(), right.clone()),
            Ast::mul(
                Ast::func("log".to_string(), vec![left.clone()]),
                derivative(right, v),
            ),
        ),
        (false, false) => Ast::Num(0),
    }
}

fn diff_func_aux(name: &str, args: &[Ast], v: &str) -> Ast {
    let mut q = None;
    for (i, arg) in args.iter().enumerate() {
        let d = Ast::mul(
            Ast::func(format!("∂{}/∂x_{}", name, i), args.to_vec()),
            derivative(arg, v),
        );
        if let Some(left) = q {
            q = Some(Ast::add(left, d));
        } else {
            q = Some(d);
        }
    }
    q.unwrap_or(Ast::Num(0))
}

fn diff_func(name: &str, args: &[Ast], v: &str) -> Ast {
    match name {
        "sin" => Ast::mul(
            Ast::func("cos".to_string(), args.to_vec()),
            derivative(&args[0], v),
        ),
        "cos" => Ast::neg(Ast::mul(
            Ast::func("sin".to_string(), args.to_vec()),
            derivative(&args[0], v),
        )),
        _ => diff_func_aux(name, args, v),
    }
}

fn derivative(a: &Ast, v: &str) -> Ast {
    if !have(a, v) {
        return Ast::Num(0);
    }
    match a {
        Ast::Num(_) => Ast::Num(0),
        Ast::Ident(x) => {
            if x == v {
                Ast::Num(1)
            } else {
                Ast::Num(0)
            }
        }
        Ast::BinOp { op, left, right } => match op {
            BinOp::Add => diff_add(left, right, v),
            BinOp::Sub => diff_sub(left, right, v),
            BinOp::Mul => diff_mul(left, right, v),
            BinOp::Div => diff_div(left, right, v),
            BinOp::Rem => unimplemented!(),
            BinOp::Pow => diff_pow(left, right, v),
        },
        Ast::UniOp { op, expr } => Ast::UniOp {
            op: op.clone(),
            expr: Box::new(derivative(expr, v)),
        },
        Ast::Func { name, args } => diff_func(name, args, v),
    }
}

fn simp_add(left: Ast, right: Ast) -> Ast {
    match (left, right) {
        (Ast::Num(a), Ast::Num(b)) => Ast::Num(a + b),
        (Ast::Num(0), x) | (x, Ast::Num(0)) => x,
        (x, y) => {
            if x == y {
                Ast::mul(Ast::Num(2), x)
            } else {
                Ast::add(x, y)
            }
        }
    }
}

fn simp_sub(left: Ast, right: Ast) -> Ast {
    match (left, right) {
        (Ast::Num(a), Ast::Num(b)) => Ast::Num(a - b),
        (Ast::Num(0), x) => Ast::neg(x),
        (x, Ast::Num(0)) => x,
        (x, y) => {
            if x == y {
                Ast::Num(0)
            } else {
                Ast::sub(x, y)
            }
        }
    }
}

fn simp_mul(left: Ast, right: Ast) -> Ast {
    match (left, right) {
        (Ast::Num(a), Ast::Num(b)) => Ast::Num(a * b),
        (Ast::Num(0), _) | (_, Ast::Num(0)) => Ast::Num(0),
        (Ast::Num(1), x) | (x, Ast::Num(1)) => x,
        (x, y) => {
            if x == y {
                Ast::pow(x, Ast::Num(2))
            } else {
                Ast::mul(x, y)
            }
        }
    }
}

fn simp_div(left: Ast, right: Ast) -> Ast {
    match (left, right) {
        (Ast::Num(0), _) => Ast::Num(0),
        (x, Ast::Num(1)) => x,
        (x, y) => {
            if x == y {
                Ast::Num(1)
            } else {
                Ast::div(x, y)
            }
        }
    }
}

fn simp_pow(left: Ast, right: Ast) -> Ast {
    match (left, right) {
        // 0^0 = 1
        (_, Ast::Num(0)) => Ast::Num(1),
        (x, Ast::Num(1)) => x,
        (Ast::Num(0), _) => Ast::Num(0),
        (Ast::Num(1), _) => Ast::Num(1),
        (x, y) => Ast::pow(x, y),
    }
}

fn simp_neg(expr: Ast) -> Ast {
    match expr {
        Ast::Num(n) => Ast::Num(-n),
        Ast::UniOp { op, expr } => match op {
            UniOp::Plus => Ast::neg(*expr),
            UniOp::Neg => *expr,
        },
        x => Ast::neg(x),
    }
}

fn simp_func(name: &str, args: Vec<Ast>) -> Ast {
    Ast::func(name.to_string(), args)
}

fn simple(a: &Ast) -> Ast {
    match a {
        Ast::Num(n) => Ast::Num(*n),
        Ast::Ident(x) => Ast::Ident(x.clone()),
        Ast::BinOp { op, left, right } => match op {
            BinOp::Add => simp_add(simple(left), simple(right)),
            BinOp::Sub => simp_sub(simple(left), simple(right)),
            BinOp::Mul => simp_mul(simple(left), simple(right)),
            BinOp::Div => simp_div(simple(left), simple(right)),
            BinOp::Rem => unimplemented!(),
            BinOp::Pow => simp_pow(simple(left), simple(right)),
        },
        Ast::UniOp { op, expr } => match op {
            UniOp::Plus => simple(expr),
            UniOp::Neg => simp_neg(simple(expr)),
        },
        Ast::Func { name, args } => {
            let args = args.iter().map(simple).collect();
            simp_func(name, args)
        }
    }
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
            let ast = make_ast(parsed);
            for a in ast {
                let mut d = derivative(&a, "x");
                println!("{}", d);
                loop {
                    let nd = simple(&d);
                    if nd == d {
                        break;
                    }
                    d = nd;
                }
                println!("{}", d);
                println!("{:?}", eval(a));
            }
        } else {
            break;
        }
    }
}
