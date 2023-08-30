use std::{collections::HashMap, fmt::Display, ops::Deref};

use ir_asm_ast_isa1st::{
    abi::{FRegId, RegId},
    *,
};

use once_cell::sync::Lazy;
use typedefs::Label;

/// doesn't have line number because each line of assembly is independent
pub type Span = (usize, usize);

#[derive(Debug)]
pub struct Spanned<T> {
    pub span: Span,
    pub inner: T,
}

impl<T> Spanned<T> {
    pub fn new(span: Span, inner: T) -> Self {
        Self { span, inner }
    }
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<T: PartialEq> PartialEq for Spanned<T> {
    /// ignores span.
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

pub type Line<'input> = Spanned<LineKind<'input>>;

#[derive(Debug, PartialEq)]
pub enum LineKind<'input> {
    Instr(InstrCall<'input>),
    Directive(DirectiveCall),
    SectionBegin(SectionKind),
    LabelDef(Spanned<&'input str>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum LineType {
    Instr,
    Directive,
    SectionBegin,
    LabelDef,
}

impl<'input> LineKind<'input> {
    pub fn kind(&self) -> LineType {
        match self {
            LineKind::Instr(_) => LineType::Instr,
            LineKind::Directive(_) => LineType::Directive,
            LineKind::SectionBegin(_) => LineType::SectionBegin,
            LineKind::LabelDef(_) => LineType::LabelDef,
        }
    }
}

impl Display for LineType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            LineType::Instr => "instruction",
            LineType::Directive => "directive",
            LineType::SectionBegin => "beginning of section",
            LineType::LabelDef => "label definition",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DirectiveCall {
    Skip,
}

pub type SectionBegin = Spanned<SectionKind>;

#[derive(Debug, PartialEq, Clone)]
pub enum SectionKind {
    Text,
    Data,
}

impl Display for SectionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            SectionKind::Text => ".text",
            SectionKind::Data => ".data",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, PartialEq)]
pub struct InstrCall<'input, T = Expr<'input>> {
    name: Spanned<&'input str>,
    arg: Vec<T>,
}

#[derive(Debug, PartialEq)]
pub enum ExprKind<'input> {
    Ident(Spanned<&'input str>),
    Const(i32),
    Relative(Spanned<&'input str>, i32),
}

impl<'a> Display for ExprKind<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprKind::Ident(i) => write!(f, "identifier `{i}`"),
            ExprKind::Const(c) => write!(f, "constant `{c}`"),
            ExprKind::Relative(i, c) => write!(f, "relative `{c}({i})`"),
        }
    }
}

pub type Expr<'input> = Spanned<ExprKind<'input>>;

#[derive(Debug, PartialEq)]
pub enum ValueType {
    Register,
    FRegister,
    RegImm,
    Immediate,
    Offset,
    Label,
}

impl Display for ValueType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ValueType::Register => "register",
            ValueType::FRegister => "float register",
            ValueType::RegImm => "relative",
            ValueType::Immediate => "immediate",
            ValueType::Offset => "offset",
            ValueType::Label => "label",
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, PartialEq)]
pub enum Value<'input> {
    Register(RegId),
    FRegister(FRegId),
    RegImm(RegId, i32),
    Immediate(i32),
    Offset(Offset<Label<'input>>),
    Label(Label<'input>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum InstrKind {
    Nullary(NullaryKind),
    Unary(UnaryKind),
    UnaryF(UnaryFKind),
    UnaryOffset(UnaryOffsetKind),
    Binary(BinaryKind),
    BinaryF(BinaryFKind),
    BinaryImm(BinaryImmKind),
    BinaryRegImm(BinaryRegImmKind),
    BinaryOffset(BinaryOffsetKind),
    BinaryFOffset(BinaryFOffsetKind),
    BinaryLabel(BinaryLabelKind),
    BinaryFLabel(BinaryFLabelKind),
    BinaryFRegImm(BinaryFRegImmKind),
    Ternary(TernaryKind),
    TernaryF(TernaryFKind),
    TernaryImm(TernaryImmKind),
    TernaryOffset(TernaryOffsetKind),
    TernaryFOffset(TernaryFOffsetKind),
}

impl<'input> Value<'input> {
    fn into_register(self) -> RegId {
        match self {
            Self::Register(r) => r,
            _ => unreachable!(),
        }
    }
    fn into_f_register(self) -> FRegId {
        match self {
            Self::FRegister(r) => r,
            _ => unreachable!(),
        }
    }
    fn into_regimm(self) -> (RegId, i32) {
        match self {
            Self::RegImm(r, i) => (r, i),
            _ => unreachable!(),
        }
    }
    fn into_imm(self) -> i32 {
        match self {
            Self::Immediate(i) => i,
            _ => unreachable!(),
        }
    }
    fn into_offset(self) -> Offset<Label<'input>> {
        match self {
            Self::Offset(name) => name,
            _ => unreachable!(),
        }
    }
    fn into_label(self) -> Label<'input> {
        match self {
            Self::Label(name) => name,
            _ => unreachable!(),
        }
    }
}

peg::parser!( pub grammar asm() for str {
    pub rule line() -> Option<Line<'input>>
        = _ lo:position!()
            inner:(label() / section_begin() / directive() / instr())?
            hi:position!() _
            { inner.map(|inner| Spanned::new((lo, hi), inner)) }

    rule number() -> i32
        = n:$(quiet!{"-"? ['0'..='9']+}) { n.parse().unwrap() }
        / expected!("number")

    rule unsigned() -> u32
        = n:$(quiet!{['0'..='9']+}) { n.parse().unwrap() }
        / expected!("unsigned")

    rule ident() -> Spanned<&'input str>
        = lo:position!() inner:$(quiet!{
            [ 'a'..='z' | 'A'..='Z' ][ 'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '.' ]*
        }) hi:position!() { Spanned::new((lo, hi), inner) }
        / expected!("identifier")

    rule label_ident() -> Spanned<&'input str>
        = lo:position!() inner:$(quiet!{"."? ident()}) hi:position!()
            { Spanned::new((lo, hi), inner) }
        / expected!("label")

    rule comment() = "#" __

    rule __() = [_]*

    rule _() = [' ' | '\t' | '\r' | '\n']* comment()?

    rule label() -> LineKind<'input>
        = name:label_ident() ":"
        { LineKind::LabelDef(name) }

    pub rule section_begin() -> LineKind<'input>
        = ".text" { LineKind::SectionBegin(SectionKind::Text) }
        / ".data" { LineKind::SectionBegin(SectionKind::Data) }

    pub rule directive() -> LineKind<'input>
        = "." label_ident() __ { LineKind::Directive(DirectiveCall::Skip) }

    rule d_arith() -> Offset<Spanned<&'input str>> = precedence!{
        x:(@) _ "+" _ y:@ { Offset::Add(Box::new(x), Box::new(y)) }
        x:(@) _ "-" _ y:@ { Offset::Sub(Box::new(x), Box::new(y)) }
        --
        l:label_ident() { Offset::Label(l) }
        n:unsigned() { Offset::Const(n) }
        "(" _ e:d_arith() _ ")" { e }
    }

    rule instr() -> LineKind<'input>
        = name:ident() _ arg:(expr() ** (_ "," _))
        { LineKind::Instr(InstrCall{
            name,
            arg
        }) }

    rule expr() -> Expr<'input>
        = lo:position!() inner:expr_() hi:position!()
        { Spanned::new((lo, hi), inner) }

    rule expr_() -> ExprKind<'input>
        = i:label_ident() { ExprKind::Ident(i) }
        / n:number() r:after_num(n) { r }

    rule after_num(n: i32) -> ExprKind<'input>
        = "(" i:ident() ")" { ExprKind::Relative(i, n) }
        / { ExprKind::Const(n) }
});

#[derive(Debug, PartialEq)]
pub enum VerifyError<'input> {
    MismatchArgs {
        at: u32,
        expect: ValueType,
        actual: Expr<'input>,
    },
    MismatchArgsCount {
        line_span: Span,
        expect_len: usize,
        actual_len: usize,
    },
    UnsupportedInstr {
        name: Spanned<&'input str>,
    },
    InvalidRegName {
        actual: Spanned<&'input str>,
    },
}

fn plural_args(n: usize) -> &'static str {
    match n {
        1 => " argument",
        _ => " arguments",
    }
}

impl<'a> Display for VerifyError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerifyError::MismatchArgs {
                at,
                expect,
                actual: Expr { span: _, inner },
            } => {
                write!(
                    f,
                    "mismatched types expected `{expect}`, found {inner} at argument position {at}"
                )
            }
            VerifyError::MismatchArgsCount {
                line_span: _,
                expect_len,
                actual_len,
            } => {
                let args1 = plural_args(*expect_len);
                let args2 = plural_args(*actual_len);
                write!(
                    f,
                    "this instruction takes {expect_len}{args1} but {actual_len}{args2} was supplied"
                )
            }
            VerifyError::UnsupportedInstr { name } => {
                write!(f, "instruction `{name}` is not supported")
            }
            VerifyError::InvalidRegName { actual } => {
                write!(
                    f,
                    "register name `{actual}` is not an ABI name or not supported"
                )
            }
        }
    }
}

type Result<'input, T> = std::result::Result<T, VerifyError<'input>>;

static ABINAME_TABLE: Lazy<HashMap<&str, u32>> = Lazy::new(|| {
    HashMap::from([
        ("s0", 8),
        ("fp", 8),
        ("zero", 0),
        ("ra", 1),
        ("sp", 2),
        ("gp", 3),
        ("hp", 4),
        ("t0", 5),
        ("t1", 6),
        ("t2", 7),
        ("s1", 9),
        ("a0", 10),
        ("a1", 11),
        ("a2", 12),
        ("a3", 13),
        ("a4", 14),
        ("a5", 15),
        ("a6", 16),
        ("a7", 17),
        ("s2", 18),
        ("s3", 19),
        ("s4", 20),
        ("s5", 21),
        ("s6", 22),
        ("s7", 23),
        ("s8", 24),
        ("s9", 25),
        ("s10", 26),
        ("s11", 27),
        ("t3", 28),
        ("t4", 29),
        ("t5", 30),
        ("t6", 31),
    ])
});

static F_ABINAME_TABLE: Lazy<HashMap<&str, u32>> = Lazy::new(|| {
    HashMap::from([
        ("fzero", 0),
        ("fone", 1),
        ("ft2", 2),
        ("ft3", 3),
        ("ft4", 4),
        ("ft5", 5),
        ("ft6", 6),
        ("ft7", 7),
        ("fs0", 8),
        ("fs1", 9),
        ("fa0", 10),
        ("fa1", 11),
        ("fa2", 12),
        ("fa3", 13),
        ("fa4", 14),
        ("fa5", 15),
        ("fa6", 16),
        ("fa7", 17),
        ("fs2", 18),
        ("fs3", 19),
        ("fs4", 20),
        ("fs5", 21),
        ("fs6", 22),
        ("fs7", 23),
        ("fs8", 24),
        ("fs9", 25),
        ("fs10", 26),
        ("fs11", 27),
        ("ft8", 28),
        ("ft9", 29),
        ("ft10", 30),
        ("ft11", 31),
    ])
});

fn get_id_from_abiname(name: Spanned<&str>) -> Result<RegId> {
    let id = ABINAME_TABLE.get(name.inner);
    id.map(Clone::clone)
        .ok_or(VerifyError::InvalidRegName { actual: name })
        .map(RegId::new)
}

fn get_f_id_from_abiname(name: Spanned<&str>) -> Result<FRegId> {
    let id = F_ABINAME_TABLE.get(name.inner);
    id.map(Clone::clone)
        .ok_or(VerifyError::InvalidRegName { actual: name })
        .map(FRegId::new)
}

fn assume_type(at: u32, e: Expr, ty: ValueType) -> Result<Value> {
    use ExprKind::*;
    use ValueType::*;
    Ok(match (ty, e.inner) {
        (Register, Ident(ident)) => {
            let r = get_id_from_abiname(ident)?;
            Value::Register(r)
        }
        (FRegister, Ident(ident)) => {
            let r = get_f_id_from_abiname(ident)?;
            Value::FRegister(r)
        }
        (RegImm, Relative(ident, d)) => {
            let r = get_id_from_abiname(ident)?;
            Value::RegImm(r, d)
        }
        (Immediate, Const(c)) => Value::Immediate(c),
        (Offset, Ident(s)) => Value::Offset(ir_asm_ast_isa1st::Offset::Label(
            typedefs::Label::raw_name(*s),
        )),
        (Label, Ident(s)) => Value::Label(typedefs::Label::raw_name(*s)),
        (expect, inner) => Err(VerifyError::MismatchArgs {
            at,
            expect,
            actual: Expr {
                span: e.span,
                inner,
            },
        })?,
    })
}

static INSTR_KIND: Lazy<HashMap<&str, InstrKind>> = Lazy::new(|| {
    use BinaryFKind::*;
    use BinaryFLabelKind::*;
    use BinaryFOffsetKind::*;
    use BinaryFRegImmKind::*;
    use BinaryImmKind::*;
    use BinaryKind::*;
    use BinaryLabelKind::*;
    use BinaryOffsetKind::*;
    use BinaryRegImmKind::*;
    use InstrKind::*;
    use NullaryKind::*;
    use TernaryFKind::*;
    use TernaryFOffsetKind::*;
    use TernaryImmKind::*;
    use TernaryKind::*;
    use TernaryOffsetKind::*;
    use UnaryFKind::*;
    use UnaryKind::*;
    use UnaryOffsetKind::*;
    HashMap::from([
        ("nop", Nullary(Nop)),
        ("j", UnaryOffset(J)),
        ("jal", UnaryOffset(Jal)),
        ("jr", Unary(Jr)),
        ("jalr", Unary(Jalr)),
        ("ret", Nullary(Ret)),
        ("mv", Binary(Mv)),
        #[cfg(not(feature = "isa_2nd"))]
        ("neg", Binary(Neg)),
        ("fmv", BinaryF(Fmv)),
        ("fneg", BinaryF(Fneg)),
        ("li", BinaryImm(Li)),
        ("beqz", BinaryOffset(Beqz)),
        ("bnez", BinaryOffset(Bnez)),
        ("bltz", BinaryOffset(Bltz)),
        ("blez", BinaryOffset(Blez)),
        ("bgtz", BinaryOffset(Bgtz)),
        ("bgez", BinaryOffset(Bgez)),
        ("lwl", BinaryLabel(LoadFromLabel)),
        ("flwl", BinaryFLabel(FLoadFromLabel)),
        ("add", Ternary(Add)),
        #[cfg(not(feature = "isa_2nd"))]
        ("sub", Ternary(Sub)),
        ("xor", Ternary(Xor)),
        #[cfg(not(feature = "isa_2nd"))]
        ("or", Ternary(Or)),
        #[cfg(not(feature = "isa_2nd"))]
        ("and", Ternary(And)),
        #[cfg(not(feature = "isa_2nd"))]
        ("sll", Ternary(Sll)),
        #[cfg(not(feature = "isa_2nd"))]
        ("sra", Ternary(Sra)),
        #[cfg(not(feature = "isa_2nd"))]
        ("slt", Ternary(Slt)),
        ("addi", TernaryImm(Addi)),
        ("subi", TernaryImm(Subi)),
        ("xori", TernaryImm(Xori)),
        #[cfg(not(feature = "isa_2nd"))]
        ("ori", TernaryImm(Ori)),
        #[cfg(not(feature = "isa_2nd"))]
        ("andi", TernaryImm(Andi)),
        ("slli", TernaryImm(Slli)),
        #[cfg(not(feature = "isa_2nd"))]
        ("srai", TernaryImm(Srai)),
        #[cfg(not(feature = "isa_2nd"))]
        ("slti", TernaryImm(Slti)),
        ("sw", BinaryRegImm(Sw)),
        ("lw", BinaryRegImm(Lw)),
        ("fsw", BinaryFRegImm(Fsw)),
        ("flw", BinaryFRegImm(Flw)),
        ("beq", TernaryOffset(Beq)),
        ("bne", TernaryOffset(Bne)),
        ("blt", TernaryOffset(Blt)),
        ("ble", TernaryOffset(Ble)),
        ("bgt", TernaryOffset(Bgt)),
        ("bge", TernaryOffset(Bge)),
        ("fblt", TernaryFOffset(Fblt)),
        ("fble", TernaryFOffset(Fble)),
        ("fbgt", TernaryFOffset(Fbgt)),
        ("fbge", TernaryFOffset(Fbge)),
        ("fbeqz", BinaryFOffset(Fbeqz)),
        ("fbnez", BinaryFOffset(Fbnez)),
        ("fbltz", BinaryFOffset(Fbltz)),
        ("fblez", BinaryFOffset(Fblez)),
        ("fbgtz", BinaryFOffset(Fbgtz)),
        ("fbgez", BinaryFOffset(Fbgez)),
        ("inw", Unary(Inw)),
        ("outb", Unary(Outb)),
        ("finw", UnaryF(Finw)),
        ("fmv", BinaryF(Fmv)),
        ("fhalf", BinaryF(Fhalf)),
        ("fadd", TernaryF(Fadd)),
        ("fmul", TernaryF(Fmul)),
        ("fsub", TernaryF(Fsub)),
    ])
});

fn get_instr_kind(name: Spanned<&str>) -> Result<InstrKind> {
    let kind = INSTR_KIND.get(name.inner);
    kind.map(Clone::clone)
        .ok_or(VerifyError::UnsupportedInstr { name })
}

pub fn verify_instr_call<'input>(
    span: Span,
    c: InstrCall<'input, Expr<'input>>,
) -> Result<Instr<Offset<Label>, Label>> {
    let len = c.arg.len();
    let arg = c.arg;
    macro_rules! assert_args_count {
        ($len:ident == $l:literal) => {
            if $len != $l {
                return Err(VerifyError::MismatchArgsCount {
                    line_span: span,
                    expect_len: $l,
                    actual_len: $len,
                });
            }
        };
    }
    macro_rules! get_arg_as {
        ($len:literal $($t:tt)*) => {
            assert_args_count!(len == $len);
            let mut it = arg.into_iter();
            get_arg_as_tt!([0, it] $($t)*);
        };
    }
    macro_rules! get_arg_as_tt {
        ([$index:expr, $it:ident] $(,)?) => {};
        ([$index:expr, $it:ident] , $a:pat => $k:ident $($t:tt)*) => {
            let $a = {
                let a = assume_type($index, $it.next().unwrap(), get_arg_as_tt!(ty[$k]))?;
                get_arg_as_tt!(a, cast[$k])
            };
            get_arg_as_tt!([$index + 1, $it] $($t)*);
        };
        (ty[imm]) => {
            ValueType::Immediate
        };
        (ty[reg]) => {
            ValueType::Register
        };
        (ty[freg]) => {
            ValueType::FRegister
        };
        (ty[regimm]) => {
            ValueType::RegImm
        };
        (ty[offset]) => {
            ValueType::Offset
        };
        (ty[label]) => {
            ValueType::Label
        };
        ($e:ident, cast[imm]) => {
            $e.into_imm()
        };
        ($e:ident, cast[reg]) => {
            $e.into_register()
        };
        ($e:ident, cast[freg]) => {
            $e.into_f_register()
        };
        ($e:ident, cast[regimm]) => {
            $e.into_regimm()
        };
        ($e:ident, cast[offset]) => {
            $e.into_offset()
        };
        ($e:ident, cast[label]) => {
            $e.into_label()
        };
    }
    let instr = get_instr_kind(c.name)?;
    use Instr::*;
    Ok(match instr {
        InstrKind::Nullary(n) => {
            assert_args_count!(len == 0);
            Nullary(n)
        }
        InstrKind::Unary(u) => {
            get_arg_as!(1, arg1 => reg);
            Unary(u, arg1)
        }
        InstrKind::UnaryF(u) => {
            get_arg_as!(1, arg1 => freg);
            UnaryF(u, arg1)
        }
        InstrKind::UnaryOffset(u) => {
            get_arg_as!(1, arg1 => offset);
            UnaryOffset(u, arg1)
        }
        InstrKind::Binary(b) => {
            get_arg_as!(2, arg1 => reg, arg2 => reg);
            Binary(b, arg1, arg2)
        }
        InstrKind::BinaryF(b) => {
            get_arg_as!(2, arg1 => freg, arg2 => freg);
            BinaryF(b, arg1, arg2)
        }
        InstrKind::BinaryImm(b) => {
            get_arg_as!(2, arg1 => reg, arg2 => imm);
            BinaryImm(b, arg1, arg2)
        }
        InstrKind::BinaryRegImm(t) => {
            get_arg_as!(2, arg1 => reg, (arg2, arg3) => regimm);
            BinaryRegImm(t, Default::default(), arg1, arg2, arg3)
        }
        InstrKind::BinaryFRegImm(t) => {
            get_arg_as!(2, arg1 => freg, (arg2, arg3) => regimm);
            BinaryFRegImm(t, Default::default(), arg1, arg2, arg3)
        }
        InstrKind::BinaryOffset(b) => {
            get_arg_as!(2, arg1 => reg, arg2 => offset);
            BinaryOffset(b, arg1, arg2)
        }
        InstrKind::BinaryFOffset(b) => {
            get_arg_as!(2, arg1 => freg, arg2 => offset);
            BinaryFOffset(b, arg1, arg2)
        }
        InstrKind::BinaryLabel(b) => {
            get_arg_as!(2, arg1 => reg, arg2 => label);
            BinaryLabel(b, arg1, arg2)
        }
        InstrKind::BinaryFLabel(b) => {
            get_arg_as!(2, arg1 => freg, arg2 => label);
            BinaryFLabel(b, arg1, arg2)
        }
        InstrKind::Ternary(t) => {
            get_arg_as!(3, arg1 => reg, arg2 => reg, arg3 => reg);
            Ternary(t, arg1, arg2, arg3)
        }
        InstrKind::TernaryF(t) => {
            get_arg_as!(3, arg1 => freg, arg2 => freg, arg3 => freg);
            TernaryF(t, arg1, arg2, arg3)
        }
        InstrKind::TernaryImm(t) => {
            get_arg_as!(3, arg1 => reg, arg2 => reg, arg3 => imm);
            TernaryImm(t, arg1, arg2, arg3)
        }
        InstrKind::TernaryOffset(t) => {
            get_arg_as!(3, arg1 => reg, arg2 => reg, arg3 => offset);
            TernaryOffset(t, arg1, arg2, arg3)
        }
        InstrKind::TernaryFOffset(t) => {
            get_arg_as!(3, arg1 => freg, arg2 => freg, arg3 => offset);
            TernaryFOffset(t, arg1, arg2, arg3)
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unknown<T>(inner: T) -> Spanned<T> {
        Spanned {
            span: (0, 0),
            inner,
        }
    }

    #[test]
    fn test_parse_instrs() {
        use ExprKind::*;
        use LineKind::*;
        assert_eq!(
            asm::line("nop  # comment").unwrap().unwrap(),
            unknown(Instr(InstrCall {
                name: unknown("nop"),
                arg: vec![]
            }))
        );
        assert_eq!(
            asm::line("addi x0, x0, 0").unwrap().unwrap(),
            unknown(Instr(InstrCall {
                name: unknown("addi"),
                arg: vec![Ident(unknown("x0")), Ident(unknown("x0")), Const(0),]
                    .into_iter()
                    .map(unknown)
                    .collect()
            }))
        );
        assert_eq!(
            asm::line("sw x1, -4(x2)").unwrap().unwrap(),
            unknown(Instr(InstrCall {
                name: unknown("sw"),
                arg: vec![Ident(unknown("x1")), Relative(unknown("x2"), -4)]
                    .into_iter()
                    .map(unknown)
                    .collect()
            }))
        );
        assert_eq!(
            asm::line("outb a0").unwrap().unwrap(),
            unknown(Instr(InstrCall {
                name: unknown("outb"),
                arg: vec![Ident(unknown("a0"))]
                    .into_iter()
                    .map(unknown)
                    .collect()
            }))
        );
    }
    #[test]
    fn test_verify_instrs() {
        use ExprKind::*;
        assert_eq!(
            verify_instr_call(
                (0, 0),
                InstrCall {
                    name: unknown("nop"),
                    arg: vec![]
                },
            )
            .unwrap(),
            ::ir_asm_ast_isa1st::Instr::Nullary(NullaryKind::Nop)
        );
        assert_eq!(
            verify_instr_call(
                (0, 0),
                InstrCall {
                    name: unknown("addi"),
                    arg: vec![Ident(unknown("zero")), Ident(unknown("sp")), Const(-4)]
                        .into_iter()
                        .map(unknown)
                        .collect()
                }
            )
            .unwrap(),
            ::ir_asm_ast_isa1st::Instr::TernaryImm(
                TernaryImmKind::Addi,
                RegId::new(0),
                RegId::new(2),
                -4
            )
        );
        assert_eq!(
            verify_instr_call(
                (0, 0),
                InstrCall {
                    name: unknown("sw"),
                    arg: vec![Ident(unknown("a1")), Relative(unknown("a2"), -4)]
                        .into_iter()
                        .map(unknown)
                        .collect()
                }
            )
            .unwrap(),
            ::ir_asm_ast_isa1st::Instr::BinaryRegImm(
                BinaryRegImmKind::Sw,
                Default::default(),
                get_id_from_abiname(unknown("a1")).unwrap(),
                get_id_from_abiname(unknown("a2")).unwrap(),
                -4
            )
        );
        assert_eq!(
            verify_instr_call(
                (0, 0),
                InstrCall {
                    name: unknown("finw"),
                    arg: vec![Ident(unknown("fa0"))]
                        .into_iter()
                        .map(unknown)
                        .collect()
                }
            )
            .unwrap(),
            ::ir_asm_ast_isa1st::Instr::UnaryF(UnaryFKind::Finw, FRegId::new(10))
        );
    }
    #[test]
    fn test_parse_label() {
        use LineKind::*;
        assert_eq!(
            asm::line("main:").unwrap().unwrap(),
            unknown(LabelDef(unknown("main")))
        );
        assert_eq!(
            asm::line(".L1:").unwrap().unwrap(),
            unknown(LabelDef(unknown(".L1")))
        );
    }
    #[test]
    fn test_parse_section() {
        use LineKind::*;
        assert_eq!(
            asm::section_begin(".text").unwrap(),
            SectionBegin(SectionKind::Text)
        );
    }
    #[test]
    fn test_get_id_from_abiname() {
        assert_eq!(get_id_from_abiname(unknown("zero")).unwrap(), RegId::new(0))
    }
}
