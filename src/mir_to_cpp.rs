use crate::mir::{BinaryOperator, EntryPoint, Literal, Operand, Place, Rvalue, SeqBlock, Statement, Terminator, UnaryOperator};
use crate::types::{Type, PrimitiveType};
use std::collections::{HashMap, VecDeque};
pub(crate)  struct MirToCppConverter<'blk> {
    cpp_code: String,
    types: HashMap<Place, Type>,
    block_labels: HashMap<&'blk SeqBlock<'blk>, String>,
}

impl<'blk> MirToCppConverter<'blk> {
    pub fn new(types: HashMap<Place, Type>) -> Self {
        Self {
            cpp_code: String::new(),
            types,
            block_labels: HashMap::new(),
        }
    }

    pub fn convert(&mut self, entry_point: EntryPoint<'blk>) -> String {
        let blocks = entry_point.seq_front.decendants();
        self.header();
        self.cpp_code.push_str("int main() {\n");
        for block in blocks {
            self.convert_seqblock(block);
        }
        self.cpp_code.push_str("    return 0;\n");
        self.cpp_code.push_str("}\n");
        self.cpp_code.clone()
    }

    fn header(&mut self) {
        self.cpp_code += r##"
#include <string>
class Unit {};
"##;
    }

    fn label_of(&mut self, seq_block: &'blk SeqBlock<'blk>) -> String {
        let label_len = self.block_labels.len();
        self.block_labels.entry(seq_block).or_insert_with(|| {
            format!("block_{}", label_len)
        }).clone()
    }

    fn convert_seqblock(&mut self, seq_block: &'blk SeqBlock<'blk>) {
        let label = self.label_of(seq_block);
        self.cpp_code.push_str(&format!("{}:\n", label));
        self.convert_statements(&*seq_block.statements.borrow());
        self.convert_terminator(&*seq_block.terminator.borrow());
    }

    fn convert_statements(&mut self, statements: &VecDeque<Statement>) {
        for statement in statements {
            self.convert_statement(statement);
        }
    }

    fn convert_terminator(&mut self, terminator: &Terminator<'blk>) {
        match terminator {
            Terminator::Return(operand) => {
                self.cpp_code.push_str(format!("    return {};\n", self.convert_operand(operand)).as_str());
            }
            Terminator::Goto(block) => {
                let label = self.label_of(*block);
                self.cpp_code.push_str(&format!("    goto {};\n", label));
            }
            Terminator::IfElse { cond, then, otherwise } => {
                let cond_str = self.convert_operand(cond);
                let then_label = self.label_of(*then);
                let otherwise_label = self.label_of(*otherwise);
                self.cpp_code.push_str(&format!("    if ({}) goto {};\nelse goto {};", cond_str, then_label, otherwise_label));
            }
        }
    }

    fn convert_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::Expr(rvalue) => {
                let cpp_expr = self.convert_rvalue(rvalue);
                self.cpp_code.push_str(&format!("    {};\n", cpp_expr));
            }
            Statement::Drop(_) => { } //C++ではdropは不要
            Statement::CopyBinding { from, to } => {
                let from_str = self.convert_operand(from);
                let to_str = self.convert_place(to);
                let ty = &self.types[to];
                let cpp_type = self.convert_type(ty);
                self.cpp_code.push_str(&format!("    {} {} = {};\n", cpp_type, to_str, from_str));
            }
            Statement::MoveBinding { from, to } => {
                let from_str = self.convert_operand(from);
                let to_str = self.convert_place(to);
                let ty = &self.types[to];
                let cpp_type = self.convert_type(ty);
                self.cpp_code.push_str(&format!("    {} {} = std::move({});\n", cpp_type, to_str, from_str));
            }
            Statement::CopyAssign { from, to } => {
                let from_str = self.convert_operand(from);
                let to_str = self.convert_place(to);
                self.cpp_code.push_str(&format!("    {} = {};\n", to_str, from_str));
            }
            Statement::MoveAssign { from, to } => {
                let from_str = self.convert_operand(from);
                let to_str = self.convert_place(to);
                self.cpp_code.push_str(&format!("    {} = std::move({});\n", to_str, from_str));
            }
        }
    }

    fn convert_rvalue(&self, rvalue: &Rvalue) -> String {
        match rvalue {
            Rvalue::BinaryOp(place, left, op, right) => {
                let l = self.convert_operand(left);
                let r = self.convert_operand(right);
                let op_str = match op {
                    BinaryOperator::Add(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "+",
                    BinaryOperator::Add(Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::String)) => "+",
                    BinaryOperator::Add(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "+",

                    BinaryOperator::Subtract(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "-",
                    BinaryOperator::Subtract(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "-",

                    BinaryOperator::Multiply(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "*",
                    BinaryOperator::Multiply(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "*",

                    BinaryOperator::Divide(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "/",
                    BinaryOperator::Divide(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "/",

                    BinaryOperator::Equal(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "==",
                    BinaryOperator::Equal(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "==",
                    BinaryOperator::Equal(Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::String)) => "==",
                    BinaryOperator::Equal(Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::Bool)) => "==",
                    BinaryOperator::Equal(Type::Primitive(PrimitiveType::Unit), Type::Primitive(PrimitiveType::Unit)) => "==",

                    BinaryOperator::NotEqual(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "!=",
                    BinaryOperator::NotEqual(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "!=",
                    BinaryOperator::NotEqual(Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::String)) => "!=",
                    BinaryOperator::NotEqual(Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::Bool)) => "!=",
                    BinaryOperator::NotEqual(Type::Primitive(PrimitiveType::Unit), Type::Primitive(PrimitiveType::Unit)) => "!=",

                    BinaryOperator::LessThan(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "<",
                    BinaryOperator::LessThan(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "<",
                    BinaryOperator::LessThan(Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::String)) => "<",

                    BinaryOperator::LessThanOrEqual(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "<=",
                    BinaryOperator::LessThanOrEqual(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => "<=",
                    BinaryOperator::LessThanOrEqual(Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::String)) => "<=",
                    
                    BinaryOperator::GreaterThan(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => ">",
                    BinaryOperator::GreaterThan(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => ">",
                    BinaryOperator::GreaterThan(Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::String)) => ">",
                    
                    BinaryOperator::GreaterThanOrEqual(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => ">=",
                    BinaryOperator::GreaterThanOrEqual(Type::Primitive(PrimitiveType::Float), Type::Primitive(PrimitiveType::Float)) => ">=",
                    BinaryOperator::GreaterThanOrEqual(Type::Primitive(PrimitiveType::String), Type::Primitive(PrimitiveType::String)) => ">=",

                    BinaryOperator::And(Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::Bool)) => "&",
                    BinaryOperator::And(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "&",
                    
                    BinaryOperator::Or(Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::Bool)) => "|",
                    BinaryOperator::Or(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "|",

                    BinaryOperator::Xor(Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::Bool)) => "^",
                    BinaryOperator::Xor(Type::Primitive(PrimitiveType::Int), Type::Primitive(PrimitiveType::Int)) => "^",

                    _ => panic!("不正な演算子: {:?}", op),
                };
                format!("{} {} = {} {} {}", self.convert_type(&self.types[place]), self.convert_place(place), l, op_str, r)
            }
            Rvalue::UnaryOperator(place, op, operand) => {
                let operand_str = self.convert_operand(operand);
                let op_str = match op {
                    UnaryOperator::Minus(Type::Primitive(PrimitiveType::Int)) => "-",
                    UnaryOperator::Minus(Type::Primitive(PrimitiveType::Float)) => "-",
                    UnaryOperator::Not(Type::Primitive(PrimitiveType::Bool)) => "!",
                    UnaryOperator::Not(Type::Primitive(PrimitiveType::Int)) => "~",
                    _ => panic!("不正な演算子: {:?}", op),
                };
                format!("{} {} = {}{}", self.convert_type(&self.types[place]), self.convert_place(place), op_str, operand_str)
            }
            Rvalue::Literal(place, lit) => {
                let lit_str = match lit {
                    Literal::Int(i) => i.to_string(),
                    Literal::Float(f) => f.to_string(),
                    Literal::String(s) => format!("\"{}\"", s),
                    Literal::Bool(b) => b.to_string(),
                    Literal::Unit => "Unit()".to_string(),
                };
                format!("{} {} = {}", self.convert_type(&self.types[place]), self.convert_place(place), lit_str)
            }
        }
    }

    fn convert_operand(&self, Operand(place): &Operand) -> String {
        self.convert_place(place)
    }

    fn convert_place(&self, place: &Place) -> String {
        format!("var_{}", place.id)
    }

    fn convert_type(&self, ty: &Type) -> String {
        match ty {
            Type::Primitive(prim) => match prim {
                PrimitiveType::Int => "int",
                PrimitiveType::Float => "double",
                PrimitiveType::String => "std::string",
                PrimitiveType::Bool => "bool",
                PrimitiveType::Unit => "Unit",
            }.to_string(),
            Type::TypeVar(_) => "auto".to_string(),
            Type::Unknown => "auto".to_string(),
            Type::FuncPointer(params, ret) => {
                let param_types = params.iter()
                    .map(|p| self.convert_type(p))
                    .collect::<Vec<_>>()
                    .join(", ");
                let ret_type = self.convert_type(ret);
                format!("std::function<{}({})>", ret_type, param_types)
            }
        }
    }
} 