use std::ops::Add;
use std::path::Iter;
use regex::Regex;
use std::str::Chars;
use colored::*;

pub mod parser;
pub mod evaluator;

#[derive(Debug, Clone)]
pub enum TokenTyp {
    Ident(String),
    PlusOperator,
    MinusOperator,
    MultiplyOperator,
    Defun,
    DivideOperator,
    NotEqualOperator,
    EqualOperator,
    While,
    Set,
    LParan,
    GreaterThan,
    GreaterOrEqualThan,
    LessThan,
    LessOrEqualThan,
    RParan,
    Add,
    Sub,
    Mul,
    Div,
    List,
    Print,
    AddKW,
    SubKW,
    MulKW,
    DivKW,
    If,
    Return,
    IntConstant(String),
    StringConstant(String),
    True,
    False,
    SingleLineComment(String),
    Error(String),
    WhiteSpace,
    NewLine,
}

pub type TokenStream = Vec<Token>;
type CharHandler = fn(&mut Lexer<'_>, chr: char) -> TokenTyp;

#[derive(Debug, Clone)]
pub struct Token {
    typ: TokenTyp,
    start: u64,
    end: u64,
}

impl Token {
    pub fn is_noise(&self) -> bool {
        match self.typ {
            TokenTyp::NewLine | TokenTyp::WhiteSpace => true,
            _ => false
        }
    }
    fn is_lparan(&self) -> bool {
        match self.typ {
            TokenTyp::LParan => true,
            _ => false
        }
    }

    fn is_rparan(&self) -> bool {
        match self.typ {
            TokenTyp::RParan => true,
            _ => false
        }
    }
}

struct Error {
    value: String
}

pub struct Lexer<'a> {
    pub source: Chars<'a>,
}

impl Lexer<'_> {
    fn peek(&self) -> Option<char> {
        self.source.clone().next()
    }

    fn consume_char(&mut self) -> Option<char> {
        self.source.next()
    }

    pub fn read_tokens(&mut self) -> Vec<Token> {
        let mut rez = Vec::new();
        while let Some(c) = self.consume_char() {
            if (c as usize) < 128 {
                rez.push(Token { typ: CHAR_HANDLERS[c as usize](self, c), start:0, end: 0 });
            } else {
                rez.push(Token {typ: TokenTyp::Error(format!("Unidentified token {}", c.to_string())), start:0, end: 0});
            }
        }
        rez
    }

    fn read_ident(&mut self, chr: char) -> String {
        let mut s = String::new();
        s.push(chr);
        while Regex::new("^([a-zA-Z]+[_]*[0-9]*|[a-zA-Z]*[_]*[a-zA-Z]+)$").unwrap().is_match(&(s.clone() + &self.peek().unwrap_or(' ').to_string())) {
            if let Some(char) = self.consume_char(){
                s.push(char);
            }
            else {
                break;
            }
        }
        s
    }

    fn read_natural_number(&mut self, chr: char) -> String {
        let mut s = String::new();
        s.push(chr);
        while Regex::new("^[0-9]*$").unwrap().is_match(&(s.clone() + &self.peek().unwrap_or(' ').to_string())) {
            if let Some(char) = self.consume_char(){
                s.push(char);
            }
            else {
                break;
            }
        }
        s
    }

    fn read_string(&mut self, chr: char) -> String {
        let mut s = String::new();
        while let Some(char) = self.consume_char() {
            if char != chr{
                s.push(char);
            }
            else {
                break;
            }
        }
        s
    }
}

#[rustfmt::skip]
static CHAR_HANDLERS: [CharHandler; 128] = [
//  0    1    2    3    4    5    6    7    8    9    A    B    C    D    E    F    //
    ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, LIN, ERR, ERR, ERR, ERR, ERR, // 0
    ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, ERR, // 1
    SPS, EXC, QOT, ERR, ERR, ERR, ERR, QOT, SYM, SYM, OP, OP, ERR, OP, ERR, OP, // 2
    DIG, DIG, DIG, DIG, DIG, DIG, DIG, DIG, DIG, DIG, ERR, ERR, LT, EQ, GT, ERR, // 3
    ERR, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, // 4
    LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, ERR, ERR, ERR, ERR, LET, // 5
    ERR, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, // 6
    LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, LET, ERR, ERR, ERR, ERR, ERR, // 7
];

const ERR: CharHandler = |lexer, chr| {
    TokenTyp::Error(chr.to_string())
};

const LET: CharHandler = |lexer, chr| {
    let s = lexer.read_ident(chr);
    match &s.to_lowercase()[..] {
        "add" => TokenTyp::AddKW,
        "defun" => TokenTyp::Defun,
        "sub" => TokenTyp::SubKW,
        "mul" => TokenTyp::MulKW,
        "div" => TokenTyp::DivKW,
        "set" => TokenTyp::Set,
        "print" => TokenTyp::Print,
        "true" => TokenTyp::True,
        "false" => TokenTyp::False,
        "while" => TokenTyp::While,
        "list" => TokenTyp::List,
        "if" => TokenTyp::If,
        "return" => TokenTyp::Return,
        _ => TokenTyp::Ident(s)
    }
};

const OP: CharHandler = |lexer, chr| {
    match chr {
        '*' => TokenTyp::Mul,
        '+' => TokenTyp::Add,
        '-' => TokenTyp::Sub,
        '/' => TokenTyp::Div,
        _ => TokenTyp::Error(format!("Unidentified token {}", chr.to_string()))
    }
};

const SYM: CharHandler = |lexer, chr| {
    match chr {
        '(' => TokenTyp::LParan,
        ')' => TokenTyp::RParan,
        _ => TokenTyp::Error(format!("Unidentified token {}", chr.to_string())),
    }
};

// [0-9]
const DIG: CharHandler = |lexer, chr| {
    TokenTyp::IntConstant(lexer.read_natural_number(chr))
};

// \s
const SPS: CharHandler = |lexer, chr| {
    TokenTyp::WhiteSpace
};

// \n
const LIN: CharHandler = |lexer, chr| {
    TokenTyp::NewLine
};

// " | '
const QOT: CharHandler = |lexer, chr| {
    TokenTyp::StringConstant(lexer.read_string(chr))
};

// =
const EQ: CharHandler = |lexer, chr| {
    TokenTyp::EqualOperator
};

// <
const LT: CharHandler = |lexer, chr| {
    if lexer.peek().is_some_and(|ch| ch == '='){
        lexer.consume_char();
        return TokenTyp::LessOrEqualThan;
    }
    return TokenTyp::LessThan;
};

// >
const GT: CharHandler = |lexer, chr| {
    if lexer.peek().is_some_and(|ch| ch == '='){
        lexer.consume_char();
        return TokenTyp::GreaterOrEqualThan;
    }
    return TokenTyp::GreaterThan;
};

// !
const EXC: CharHandler = |lexer, chr| {
    if lexer.peek().is_some_and(|ch| ch == '='){
        lexer.consume_char();
        return TokenTyp::NotEqualOperator;
    }
    panic!("Not existing token");
};
