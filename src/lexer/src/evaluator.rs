use std::collections::HashMap;
use crate::parser::Function;

#[derive(Clone, Debug)]
pub struct Context {
    pub vars: HashMap<String, Variable>,
    pub functions: HashMap<String, Function>,
    pub execution_stack: HashMap<String, Variable>,
}

#[derive(Clone, Debug)]
pub enum Variable {
    String(String),
    Int(i32),
    List(Vec<Variable>),
    Boolean(bool),
    Void
}

impl Variable {
    pub fn get_int_value(&self) -> i32 {
        match self {
            Self::Int(rez) => rez.clone(),
            _ => panic!("Variable doesn't have the int type")
        }
    }

    pub fn get_boolean_value(&self) -> bool {
        match self {
            Self::Boolean(el) => el.clone(),
            _ => panic!("Variable doesn't have the boolean type")
        }
    }
}

impl ToString for Variable {
    fn to_string(&self) -> String {
        match self {
            Self::String(val) => val.to_string(),
            Self::Int(val) => val.to_string(),
            Self::Boolean(val) => val.to_string(),
            Self::List(val) => format!("[{}]", val.iter().map(|var| var.to_string()).collect::<Vec<String>>().join(", ")).to_string()
        }
    }
}