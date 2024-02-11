#![feature(let_chains)]
use std::io::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// A token is a chunk of the input that can be parsed.
///
/// For example, the parser doesn't care about that individual
/// digits of a number, just that there is a number. The digits
/// are characters, the number is a token.
///
/// This is a simpler parser, so the only tokens we care about
/// are numbers and operators (and parentheses for grouping).
enum Token {
    Number(i64),
    Op(Op),
    LeftParen,
    RightParen,
}

#[derive(Clone, Debug)]
struct Parser {
    input: String,
    pos: usize,

    current: Option<Token>,
}

impl Parser {
    fn new(input: String) -> Self {
        Self {
            input,
            pos: 0,
            current: None,
        }
    }

    /// Read the next character, advance the position, and return
    fn advance(&mut self) -> Option<char> {
        let c = self.input.chars().nth(self.pos);
        self.pos += 1;
        c
    }

    /// Read the next character without advancing
    fn peek(&mut self) -> Option<char> {
        self.input.chars().nth(self.pos)
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Scan through a number and convert it to an integer
    fn number(&mut self) -> i64 {
        let start = self.pos - 1;
        while let Some(c) = self.peek() {
            if !c.is_ascii_digit() {
                break;
            }

            self.advance();
        }

        self.input[start..self.pos].parse().unwrap()
    }

    /// Get the next token, advancing the position
    fn token(&mut self) -> Option<Token> {
        self.skip_whitespace();
        let tok = match self.advance() {
            Some('0'..='9') => Some(Token::Number(self.number())),

            Some('+') => Some(Token::Op(Op::Plus)),
            Some('-') => Some(Token::Op(Op::Minus)),
            Some('*') => Some(Token::Op(Op::Times)),
            Some('/') => Some(Token::Op(Op::Divide)),
            Some('(') => Some(Token::LeftParen),
            Some(')') => Some(Token::RightParen),

            _ => None,
        };

        self.current = tok;
        tok
    }

    /// Get the next token without advancing
    fn peek_token(&mut self) -> Option<Token> {
        let mut copy = self.clone();
        copy.token()
    }

    /// Consume the next token if it matches, or else return an error
    fn consume(&mut self, token: Token) -> Result<(), ParseError> {
        match self.token() {
            Some(t) if t == token => Ok(()),
            _ => Err(self.error(ParseErrorKind::UnexpectedToken)),
        }
    }

    /// Parse an expression with the given precedence (using pratt parsing)
    ///
    /// This function does the heavily lifting of the expression parser. Using
    /// "precedence", it implements order of operations.
    ///
    /// This implementation is inspired by [Matklad's blog post](https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html)
    fn parse_precedence(&mut self, precedence: u8) -> Result<Expression, ParseError> {
        let Some(token) = self.token() else {
            return Err(self.error(ParseErrorKind::UnexpectedEnd));
        };

        let mut lhs = match token {
            Token::Number(n) => Expression::Number(n),
            Token::LeftParen => {
                let lhs = self.parse_precedence(0)?;
                self.consume(Token::RightParen)?;
                lhs
            }
            Token::Op(op) => {
                let Some(((), r_bp)) = Self::prefix_binding_power(op) else {
                    return Err(self.error(ParseErrorKind::NotAnExpression));
                };
                let rhs = self.parse_precedence(r_bp)?;

                Expression::Prefix {
                    rhs: Box::new(rhs),
                    op: op,
                }
            }
            _ => return Err(self.error(ParseErrorKind::NotAnExpression)),
        };

        loop {
            let op = match self.peek_token() {
                Some(Token::Op(op)) => op,
                Some(Token::RightParen) | None => break,
                t => {
                    eprintln!("not an infix expression: {:?}", t);
                    return Err(self.error(ParseErrorKind::NotAnExpression));
                }
            };

            if let Some((l_bp, r_bp)) = Self::infix_binding_power(op) {
                if l_bp < precedence {
                    break;
                }
                self.token();
                lhs = Expression::Infix {
                    lhs: Box::new(lhs),
                    rhs: Box::new(self.parse_precedence(r_bp)?),
                    op,
                };
                continue;
            }

            break;
        }

        Ok(lhs)
    }

    pub fn parse(&mut self) -> Result<Expression, ParseError> {
        self.parse_precedence(0)
    }

    fn prefix_binding_power(op: Op) -> Option<((), u8)> {
        match op {
            Op::Plus | Op::Minus => Some(((), 9)),
            _ => None,
        }
    }

    fn infix_binding_power(op: Op) -> Option<(u8, u8)> {
        match op {
            Op::Plus | Op::Minus => Some((5, 6)),
            Op::Times | Op::Divide => Some((7, 8)),
        }
    }

    fn error(&self, kind: ParseErrorKind) -> ParseError {
        ParseError {
            kind,
            pos: self.pos,
        }
    }
}

fn parse(input: &str) -> Result<Expression, ParseError> {
    Parser::new(input.to_string()).parse()
}

#[derive(Debug, Clone)]
pub enum ParseErrorKind {
    UnexpectedEnd,
    NotAnExpression,
    UnexpectedToken,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    kind: ParseErrorKind,
    pos: usize,
}

#[derive(Clone, Debug)]
enum Expression {
    Number(i64),
    Infix {
        lhs: Box<Expression>,
        rhs: Box<Expression>,
        op: Op,
    },
    Prefix {
        rhs: Box<Expression>,
        op: Op,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Op {
    Plus,
    Minus,
    Times,
    Divide,
}

struct Compiler {
    internal: std::io::BufWriter<Vec<u8>>,
}

enum Register {
    Rax,
    Rbx,
    Rcx,
    Rsp,
    Rbp,
    Rdi,
    Rsi,
    Rdx,
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Register::Rax => write!(f, "rax"),
            Register::Rbx => write!(f, "rbx"),
            Register::Rcx => write!(f, "rcx"),
            Register::Rsp => write!(f, "rsp"),
            Register::Rbp => write!(f, "rbp"),
            Register::Rdi => write!(f, "rdi"),
            Register::Rsi => write!(f, "rsi"),
            Register::Rdx => write!(f, "rdx"),
        }
    }
}

impl TryFrom<&str> for Register {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "rax" => Ok(Register::Rax),
            "rbx" => Ok(Register::Rbx),
            "rcx" => Ok(Register::Rcx),
            "rsp" => Ok(Register::Rsp),
            "rbp" => Ok(Register::Rbp),
            "rdi" => Ok(Register::Rdi),
            "rsi" => Ok(Register::Rsi),
            "rdx" => Ok(Register::Rdx),
            _ => Err(()),
        }
    }
}

enum Arg {
    Register(Register),
    Number(i64),
    String(String),
}

impl From<&str> for Arg {
    fn from(s: &str) -> Self {
        match Register::try_from(s) {
            Ok(r) => Arg::Register(r),
            _ => Arg::String(s.to_string()),
        }
    }
}
impl From<i64> for Arg {
    fn from(s: i64) -> Self {
        Arg::Number(s)
    }
}

impl From<Register> for Arg {
    fn from(r: Register) -> Self {
        Arg::Register(r)
    }
}

impl std::fmt::Display for Arg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Arg::Register(r) => write!(f, "{}", r),
            Arg::Number(n) => write!(f, "{}", n),
            Arg::String(s) => write!(f, "\"{}\"", s),
        }
    }
}

struct Instruction {
    args: Vec<Arg>,
    name: String,
    comment: String,
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} ", self.name)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }

        if !self.comment.is_empty() {
            write!(f, " ; {}", self.comment)?;
        }

        Ok(())
    }
}

macro_rules! ins {
    ($s:expr, $ins:ident $($args:expr),* $(; $comment:expr)?) => {
        writeln!($s.internal, "    {}", Instruction {
            name: String::from(stringify!($ins)),
            args: vec![$(Arg::from($args)),*],
            comment: String::from(stringify!($($comment)?)),
        })
    };
}

impl Compiler {
    fn new() -> Self {
        Self {
            internal: std::io::BufWriter::new(Vec::new()),
        }
    }

    fn printf(&mut self) -> std::io::Result<()> {
        writeln!(self.internal, "    mov rdi, fmt")?;
        ins!(self, pop "rsi" ; "get stack value")?;
        ins!(self, mov "rax", 0 ; "AL = 0")?;
        writeln!(self.internal, "    call printf wrt ..plt")?;

        Ok(())
    }

    fn exit(&mut self, code: i64) -> std::io::Result<()> {
        writeln!(self.internal, "")?;
        ins!(self, mov "rax", 60 ; "syscall for exit")?;
        ins!(self, mov "rdi", code ; "exit code")?;
        ins!(self, syscall ; "invoke exit")?;

        Ok(())
    }

    fn compile(&mut self, expr: Expression) -> std::io::Result<()> {
        match expr {
            Expression::Number(n) => {
                ins!(self, mov "rax", n)?;
                ins!(self, push "rax")?;
            }
            Expression::Prefix { rhs, op } => {
                self.compile(*rhs)?;
                match op {
                    Op::Minus => {
                        ins!(self, pop "rax")?;
                        ins!(self, neg "rax")?;
                        ins!(self, push "rax")?;
                    }
                    _ => unimplemented!(),
                }
            }
            Expression::Infix { lhs, rhs, op } => {
                self.compile(*lhs)?;
                self.compile(*rhs)?;
                ins!(self, pop "rbx")?;
                ins!(self, pop "rax")?;

                match op {
                    Op::Plus => ins!(self, add "rax", "rbx")?,
                    Op::Minus => ins!(self, sub "rax", "rbx")?,
                    Op::Times => ins!(self, imul "rax", "rbx")?,
                    Op::Divide => {
                        ins!(self, xor "rdx", "rdx")?;
                        ins!(self, idiv "rbx")?;
                    }
                };

                ins!(self, push "rax" ; "put expression result on stack")?;
            }
        }
        Ok(())
    }

    fn end(&mut self) -> String {
        let contents = String::from_utf8(self.internal.buffer().to_vec()).unwrap();
        self.internal = std::io::BufWriter::new(Vec::new());

        contents
    }
}

fn main() -> std::io::Result<()> {
    let expr = parse("5 - (5 * 5)").unwrap();
    eprintln!("{:?}", expr);
    let mut compiler = Compiler::new();

    compiler.compile(expr)?;
    compiler.printf()?;
    compiler.exit(0)?;

    println!(
        r#"section .rodata
    fmt: db "%d", 0x0a, 0 ; char fmt[] = "%d\n";

    section .text
      extern printf
      global main
      default rel

      main:"#
    );
    println!("{}", compiler.end());

    Ok(())
}
