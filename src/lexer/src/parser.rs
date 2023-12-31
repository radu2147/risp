use std::collections::HashMap;
use crate::{TokenTyp, Token, Lexer};
use crate::evaluator::{Context, Variable};


#[derive(Debug, Clone)]
pub enum AstKind {
    CallStatement(Box<CallStatement>),

    IdentExpression(Box<IdentExpression>),

    AddExpression(Box<ArithmeticExpression>),
    SubExpression(Box<ArithmeticExpression>),
    MulExpression(Box<ArithmeticExpression>),
    DivExpression(Box<ArithmeticExpression>),

    IntExpression(Box<ConstantExpression>),
    ListDeclaration(Box<ListDeclaration>),
    StringExpression(Box<ConstantExpression>),
    BooleanExpression(Box<ConstantExpression>),
    BinaryExpression(Box<BinaryExpression>),

    IfStatement(Box<IfStatement>),
    PrintStatement(Box<PrintStatement>),
    DefineStatement(Box<DefineStatement>),
    ForStatement(Box<ForStatement>),

    FunctionParameters(Box<FunctionParameters>),
    FunctionDeclaration(Box<FunctionDeclaration>),

    ReturnStatement(Box<ReturnStatement>)
}

#[derive(Debug, Clone)]
enum BinaryOperator {
    NotEqualOperator,
    EqualOperator,
    LessThanOperator,
    LessOrEqualThanOperator,
    GreaterThanOperator,
    GreaterOrEqualThanOperator,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub params: Vec<Expression>,
    pub body: Vec<AstKind>
}

impl BinaryOperator {
    fn evaluate(&self, context: &Context, a: &Expression, b: &Expression) -> bool {
        match self {
            Self::EqualOperator => {
                let left = a.evaluate(context);
                let right = b.evaluate(context);

                left.get_int_value() == right.get_int_value()
            },
            Self::NotEqualOperator => {
                let left = a.evaluate(context);
                let right = b.evaluate(context);

                left.get_int_value() != right.get_int_value()
            },
            Self::LessThanOperator => {
                let left = a.evaluate(context);
                let right = b.evaluate(context);

                left.get_int_value() < right.get_int_value()
            },
            Self::LessOrEqualThanOperator => {
                let left = a.evaluate(context);
                let right = b.evaluate(context);

                left.get_int_value() <= right.get_int_value()
            },
            Self::GreaterOrEqualThanOperator => {
                let left = a.evaluate(context);
                let right = b.evaluate(context);

                left.get_int_value() >= right.get_int_value()
            },
            Self::GreaterThanOperator => {
                let left = a.evaluate(context);
                let right = b.evaluate(context);

                left.get_int_value() > right.get_int_value()
            }
        }
    }
}

impl AstKind {
    pub fn get_ident(&self) -> String {
        match self {
            Self::IdentExpression(el) => el.name.clone(),
            _ => panic!("Token {:?} doesn't have a value associated to it", self)
        }
    }

    pub fn execute(&self, context: &mut Context) {
        match self {
            Self::PrintStatement(pr_smt) => {
                let smts = pr_smt.arguments.iter().map(|x|x.evaluate(context).to_string()).collect::<Vec<String>>();
                print!("{}", smts.join(&pr_smt.separator));
            }
            Self::DefineStatement(def_smt) => {
                context.vars.insert(def_smt.receiver.clone(), def_smt.value.evaluate(context));
            },
            Self::ForStatement(for_smt) => {
                let expr = &for_smt.stop;
                while expr.evaluate(context).get_boolean_value() {
                    for_smt.statements.iter().for_each(|smt|smt.execute(context));
                }
            },
            Self::IfStatement(if_smt) => {
                match &if_smt.condition {
                    Expression::BinaryExpression(binary_expr) => {},
                    _ => panic!("This should be a logical expression")
                };
                if if_smt.condition.evaluate(context).get_boolean_value() {
                    if_smt.conditional_expression.execute(context);
                    return;
                }
                if_smt.else_expression.execute(context);
            },
            Self::FunctionDeclaration(funct_dec) => {
                if let AstKind::FunctionParameters(params) = &funct_dec.parameters {
                    context.functions.insert(funct_dec.name.clone(), Function { params: params.parameters.clone(), body: funct_dec.body.clone() });
                    return;
                }
                panic!("Wrong parsing for function parameterss")
            },
            Self::CallStatement(call_smt) => {
                if let Some(func) = context.functions.get(&call_smt.callee) {
                    if call_smt.arguments.len() != func.params.len() {
                        panic!("Wrong number of arguments");
                    }
                    for index in 0..call_smt.arguments.len() {
                        context.execution_stack.insert(func.params.get(index).unwrap().get_ident(), call_smt.arguments.get(index).unwrap().evaluate(context));
                    }
                    let clone = &mut context.clone();
                    for stmt in &func.body {
                        stmt.execute(clone);
                    }
                    for index in 0..call_smt.arguments.len() {
                        context.execution_stack.remove(&func.params.get(index).unwrap().get_ident());
                    }
                }
            }
            _ => panic!("Node {:?} not a statemnt", self)
        }
    }

    pub fn to_expression(self) -> Expression {
        match self {
            Self::DivExpression(el) => Expression::DivExpression(el),
            Self::BinaryExpression(el) => Expression::BinaryExpression(el),
            Self::AddExpression(el) => Expression::AddExpression(el),
            Self::SubExpression(el) => Expression::SubExpression(el),
            Self::MulExpression(el) => Expression::MulExpression(el),
            Self::IntExpression(el) => Expression::IntExpression(el),
            Self::ListDeclaration(el) => Expression::ListDeclaration(el),
            Self::StringExpression(el) => Expression::StringExpression(el),
            Self::BooleanExpression(el) => Expression::BooleanExpression(el),
            Self::IdentExpression(el) => Expression::IdentExpression(el),
            _ => panic!("Node {:?} is not an expression", self)
        }
    }
}


#[derive(Debug, Clone)]
enum Expression {
    IdentExpression(Box<IdentExpression>),

    AddExpression(Box<ArithmeticExpression>),
    SubExpression(Box<ArithmeticExpression>),
    MulExpression(Box<ArithmeticExpression>),
    DivExpression(Box<ArithmeticExpression>),

    IntExpression(Box<ConstantExpression>),
    StringExpression(Box<ConstantExpression>),
    BooleanExpression(Box<ConstantExpression>),
    BinaryExpression(Box<BinaryExpression>),
    ListDeclaration(Box<ListDeclaration>)
}

impl Expression {

    pub fn get_ident(&self) -> String {
        match self {
            Self::IdentExpression(el) => el.name.clone(),
            _ => panic!("Token {:?} doesn't have a value associated to it", self)
        }
    }

    pub fn evaluate(&self, context: & Context) -> Variable {
        match self {
            Self::BooleanExpression(expr) => Variable::Boolean(expr.value.parse::<bool>().unwrap()),
            Self::IntExpression(expr) => Variable::Int(expr.value.parse::<i32>().unwrap()),
            Self::StringExpression(expr) => Variable::String(expr.value.clone()),
            Self::AddExpression(add_expr) => {
                add_expr.arguments.iter().map(|expr|expr.evaluate(context)).reduce(|acc, el| {
                    match acc {
                        Variable::Int(val) => {
                            Variable::Int(val + el.get_int_value())
                        },
                        Variable::Boolean(val) => {
                            Variable::Boolean(val && el.get_boolean_value())
                        },
                        Variable::List(mut val) => {
                            val.extend(vec![el]);
                            Variable::List(val)
                        }
                        Variable::String(val) => {
                            Variable::String(val + &el.to_string())
                        }
                    }
                }).unwrap()
            },
            Self::MulExpression(mul_expr) => {
                mul_expr.arguments.iter().map(|expr|expr.evaluate(context)).reduce(|acc, el| {
                    Variable::Int(acc.get_int_value() * el.get_int_value())
                }).unwrap()
            },
            Self::DivExpression(div_expr) => {
                div_expr.arguments.iter().map(|expr|expr.evaluate(context)).reduce(|acc, el| {
                    Variable::Int(acc.get_int_value() / el.get_int_value())
                }).unwrap()
            },
            Self::SubExpression(sub_expr) => {
                sub_expr.arguments.iter().map(|expr|expr.evaluate(context)).reduce(|acc, el| {
                    Variable::Int(acc.get_int_value() - el.get_int_value())
                }).unwrap()
            },
            Self::BinaryExpression(bin_expr) => {
                Variable::Boolean(bin_expr.operator.evaluate(context, &bin_expr.left, &bin_expr.right))
            },
            Self::ListDeclaration(list_decl) => {
                Variable::List(list_decl.arguments.iter().map(|var| var.evaluate(context)).collect::<Vec<Variable>>())
            }
            Self::IdentExpression(ident_expr) => {
                if let Some(ident) = context.execution_stack.get(&ident_expr.name) {
                    return ident.clone();
                }
                if let Some(ident) = context.vars.get(&ident_expr.name) {
                    return ident.clone();
                }
                panic!("Variable {} does not exist", ident_expr.name);
            },
        }
    }
}

#[derive(Debug)]
pub struct Program {
    nodes: Vec<AstKind>
}

impl Program {
    pub fn execute_nodes(self) {
        let mut context = Context { vars: HashMap::new(), functions: HashMap::new(), execution_stack: HashMap::new() };
        self.nodes.into_iter().for_each(|node|node.execute(& mut context));
    }
}

#[derive(Debug, Clone)]
struct CallStatement {
    callee: String,
    arguments: Vec<Expression>
}

#[derive(Debug, Clone)]
struct ReturnStatement {
    argument: AstKind
}

#[derive(Debug, Clone)]
struct IdentExpression {
    name: String
}

#[derive(Debug, Clone)]
struct PrintStatement {
    arguments: Vec<Expression>,
    separator: String
}

#[derive(Debug, Clone)]
struct ForStatement {
    statements: Vec<AstKind>,
    stop: Expression
}

#[derive(Debug, Clone)]
struct DefineStatement {
    receiver: String,
    value: Expression
}

#[derive(Debug, Clone)]
struct ArithmeticExpression {
    arguments: Vec<Expression>
}

#[derive(Debug, Clone)]
struct ConstantExpression {
    value: String
}

#[derive(Debug, Clone)]
struct BinaryExpression {
    left: Expression,
    operator: BinaryOperator,
    right: Expression
}

#[derive(Debug, Clone)]
struct IfStatement {
    condition: Expression,
    conditional_expression: AstKind,
    else_expression: AstKind,
}

#[derive(Debug, Clone)]
struct FunctionParameters {
    parameters: Vec<Expression>
}

#[derive(Debug, Clone)]
struct ListDeclaration {
    arguments: Vec<Expression>
}

#[derive(Debug, Clone)]
struct FunctionDeclaration {
    parameters: AstKind,
    name: String,
    body: Vec<AstKind>
}

enum Reference {
    None,
    FunctionDeclaration
}

fn parse_until_r_paran<Container: Iterator<Item=Token> + Clone>(tokens: &mut Container, rf: Reference) -> Vec<AstKind> {
    let mut rez = Vec::new();
    while !tokens.clone().next().unwrap().is_rparan() {
        rez.push(paranthesize(tokens, &rf));
    }
    rez
}


fn paranthesize<Container: Iterator<Item=Token> + Clone>(tokens: &mut Container, rf: &Reference) -> AstKind {
    let mut token = tokens.next().unwrap();
    match token.typ {
        TokenTyp::LParan => {
            let mut rez = parse_until_r_paran(tokens, Reference::None);
            tokens.next();
            let callee = rez.remove(0);
            match callee {
                AstKind::PrintStatement(_) | AstKind::FunctionDeclaration(_) | AstKind::ListDeclaration(_) | AstKind::ForStatement(_) | AstKind::DefineStatement(_) | AstKind::IfStatement(_) | AstKind::BinaryExpression(_) | AstKind::AddExpression(_) | AstKind::MulExpression(_) | AstKind::DivExpression(_) | AstKind::SubExpression(_) => callee,
                AstKind::IdentExpression(ref ident) => {
                    match rf {
                        Reference::None => {
                            let callee = callee.get_ident();
                            AstKind::CallStatement(Box::new(CallStatement{ callee , arguments: rez.into_iter().map(|el|el.to_expression()).collect() }))
                        }
                        Reference::FunctionDeclaration => {
                            rez.insert(0, callee);
                            let parameters = rez.into_iter().map(|x|x.to_expression()).collect::<Vec<Expression>>();
                            AstKind::FunctionParameters(Box::new(FunctionParameters { parameters }))
                        }
                    }
                },
                _ => panic!("Should not reach here")
            }
        },
        TokenTyp::EqualOperator => {
            let mut arguments: Vec<Expression> = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el| el.to_expression()).collect();
            AstKind::BinaryExpression(Box::new(BinaryExpression {left: arguments.remove(0), right: arguments.remove(0), operator: BinaryOperator::EqualOperator}))
        },
        TokenTyp::NotEqualOperator => {
            let mut arguments: Vec<Expression> = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el| el.to_expression()).collect();
            AstKind::BinaryExpression(Box::new(BinaryExpression {left: arguments.remove(0), right: arguments.remove(0), operator: BinaryOperator::NotEqualOperator}))
        },
        TokenTyp::LessThan => {
            let mut arguments: Vec<Expression> = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el| el.to_expression()).collect();
            AstKind::BinaryExpression(Box::new(BinaryExpression {left: arguments.remove(0), right: arguments.remove(0), operator: BinaryOperator::LessThanOperator}))
        },
        TokenTyp::LessOrEqualThan => {
            let mut arguments: Vec<Expression> = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el| el.to_expression()).collect();
            AstKind::BinaryExpression(Box::new(BinaryExpression {left: arguments.remove(0), right: arguments.remove(0), operator: BinaryOperator::LessOrEqualThanOperator}))
        },
        TokenTyp::GreaterThan => {
            let mut arguments: Vec<Expression> = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el| el.to_expression()).collect();
            AstKind::BinaryExpression(Box::new(BinaryExpression {left: arguments.remove(0), right: arguments.remove(0), operator: BinaryOperator::GreaterThanOperator}))
        },
        TokenTyp::GreaterOrEqualThan => {
            let mut arguments: Vec<Expression> = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el| el.to_expression()).collect();
            AstKind::BinaryExpression(Box::new(BinaryExpression {left: arguments.remove(0), right: arguments.remove(0), operator: BinaryOperator::GreaterOrEqualThanOperator}))
        },
        TokenTyp::If => {
            let mut arguments = parse_until_r_paran(tokens, Reference::None);
            let condition = arguments.remove(0).to_expression();
            let consequent = arguments.remove(0);
            let alternate = arguments.remove(0);
            AstKind::IfStatement(Box::new(IfStatement { condition: condition, conditional_expression: consequent, else_expression: alternate }))
        },
        TokenTyp::True => AstKind::BooleanExpression(Box::new(ConstantExpression{ value: true.to_string()})),
        TokenTyp::False => AstKind::BooleanExpression(Box::new(ConstantExpression{ value: false.to_string()})),
        TokenTyp::IntConstant(el) => AstKind::IntExpression(Box::new(ConstantExpression{ value: el})),
        TokenTyp::StringConstant(el) => AstKind::StringExpression(Box::new(ConstantExpression{ value: el})),
        TokenTyp::Ident(el) => AstKind::IdentExpression(Box::new(IdentExpression {  name: el})),
        TokenTyp::AddKW => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::AddExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::Add => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::AddExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::SubKW => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::SubExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::Sub => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::SubExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::MulKW => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::MulExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::Mul => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::MulExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::DivKW => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::DivExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::Div => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::DivExpression(Box::new(ArithmeticExpression { arguments }))
        },
        TokenTyp::Print => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::PrintStatement(Box::new(PrintStatement {  arguments, separator: "".to_string()}))
        },
        TokenTyp::Set => {
            let mut arguments = parse_until_r_paran(tokens, Reference::None);
            let expr = arguments.remove(1);
            AstKind::DefineStatement(Box::new(DefineStatement { receiver: arguments[0].get_ident(), value: expr.to_expression()}))
        }
        TokenTyp::While => {
            let mut arguments: Vec<AstKind> = parse_until_r_paran(tokens, Reference::None);
            let stop = arguments.remove(0).to_expression();
            AstKind::ForStatement(Box::new(ForStatement { stop, statements: arguments }))
        },
        TokenTyp::List => {
            let arguments = parse_until_r_paran(tokens, Reference::None).into_iter().map(|el|el.to_expression()).collect();
            AstKind::ListDeclaration(Box::new(ListDeclaration { arguments: arguments }))
        },
        TokenTyp::Return => {
            let argument = parse_until_r_paran(tokens, Reference::None).get(0).unwrap();
            AstKind::ReturnStatement(Box::new(ReturnStatement { argument }))
        },
        TokenTyp::Defun => {
            let mut arguments = parse_until_r_paran(tokens, Reference::FunctionDeclaration);
            let name = arguments.remove(0).get_ident();
            let parameters = arguments.remove(0);
            AstKind::FunctionDeclaration(Box::new(FunctionDeclaration { parameters, name, body: arguments }))
        }
        _ => panic!("Unknown syntax")
    }
}

pub fn parse(mut lexer: Lexer) -> Program{
    let mut tokens = lexer.read_tokens().into_iter().filter(|tok| !tok.is_noise()).collect::<Vec<Token>>().into_iter();
    let mut rez = Vec::new();
    while tokens.clone().next().is_some() {
        rez.push(paranthesize(&mut tokens, &Reference::None));
    }

    Program {
        nodes: rez
    }
}