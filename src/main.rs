use lexer::{
    parser::{parse, Program},
    Lexer,
};

fn main() {
    let program: Program = parse(Lexer {
        source: r#"
    (set a "hello ")
    (print (add a "world!"))"#
            .chars()
    });
    program.execute_nodes();
}
