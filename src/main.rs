use std::{collections::HashMap, io::Read, ops::Add};

use anyhow::{anyhow, Context, Result};
use base64::Engine;
use flate2::{
    bufread::ZlibDecoder,
    read::{GzDecoder, MultiGzDecoder},
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alphanumeric1, anychar, char, multispace0},
    combinator::{fail, opt, verify},
    error::{convert_error, ErrorKind, VerboseError},
    multi::{many0, many1},
    sequence::delimited,
    IResult, Parser, Slice,
};
use nom_supreme::{
    error::ErrorTree,
    final_parser::{final_parser, Location},
    ParserExt,
};

fn decode_with_xor(b64_input: impl AsRef<[u8]>, non_b64_input: impl AsRef<[u8]>) -> Result<String> {
    let non_b64_input = base64_encode(non_b64_input)?;
    let b64_input = base64_decode(b64_input)?;
    let mut output_buffer = String::new();
    let mut outer_loop_counter = 0;
    while outer_loop_counter < b64_input.len() {
        for inner_loop_counter in 0..non_b64_input.len() {
            let curr_char = ((b64_input[outer_loop_counter] as u8)
                ^ (non_b64_input
                    .chars()
                    .nth(inner_loop_counter)
                    .ok_or_else(|| anyhow!("Reading a char from non b64 input"))?
                    as u8)) as char;
            output_buffer = format!("{}{}", output_buffer, curr_char);
            outer_loop_counter += 1;
            if outer_loop_counter >= b64_input.len() {
                break;
            };
        }
    }
    return gzuncompress(&base64_decode(&output_buffer)?);
}

type PResult<I, O> = IResult<I, O, ErrorTree<I>>;

fn parse_var(i: &str) -> PResult<&str, VName> {
    let (i, _) = char('$').parse(i)?;
    let (i, name) = alphanumeric1(i)?;
    Ok((i, VName(name.to_string())))
}

fn parse_b64_string_content(i: &str) -> PResult<&str, Vec<char>> {
    many1(verify(anychar, |&c| {
        c.is_alphanumeric() || c == '/' || c == '=' || c == '+'
    }))
    .parse(i)
}

fn parse_b64_string(i: &str) -> PResult<&str, String> {
    let (i, out) = alt((
        delimited(char('\''), parse_b64_string_content, char('\'')),
        delimited(char('"'), parse_b64_string_content, char('"')),
    ))
    .parse(i)?;
    Ok((i, out.into_iter().collect()))
}

#[derive(Debug, Clone, PartialEq)]
enum PVal {
    Var(VName),
    StringLiteral(String),
}

#[derive(Debug, Clone, PartialEq)]
enum EVal {
    Text(String),
    Bytes(Vec<u8>),
}

impl EVal {
    fn get_val_as_bytes(&'_ self) -> impl AsRef<[u8]> + '_ {
        match self {
            EVal::Text(val) => val.as_bytes(),
            EVal::Bytes(val) => val,
        }
    }

    fn get_text(&self) -> Option<&str> {
        match self {
            EVal::Text(val) => Some(&val),
            EVal::Bytes(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Call(Call),
    Val(PVal),
}

#[derive(Debug, Clone, PartialEq)]
struct Call {
    fn_name: FName,
    args: Vec<Expr>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum FName {
    Var(VName),
    Literal(String),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct VName(String);

impl From<&str> for VName {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

#[derive(Debug, PartialEq)]
struct Env(HashMap<VName, EVal>);

impl Env {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn get(&self, key: &VName) -> Option<&EVal> {
        self.0.get(key)
    }

    fn with(self, key: VName, val: EVal) -> Self {
        let mut new_version = self;
        new_version.0.insert(key, val);
        new_version
    }

    fn with_vars(self, vars: Vec<(&str, &str)>) -> Self {
        let mut new_version = self;
        for (key, val) in vars {
            new_version
                .0
                .insert(VName(key.to_string()), EVal::Text(val.to_string()));
        }
        new_version
    }
}

fn parse_args1(i: &str) -> PResult<&str, Vec<Expr>> {
    let (i, expr) = parse_expr.context("First function argument").parse(i)?;
    let (i, tail) = many0(
        char(',')
            .and(multispace0)
            .and(parse_expr)
            .map(|(_, expr)| expr),
    )
    .parse(i)?;
    Ok((i, [vec![expr], tail].concat()))
}

fn parse_call<'a>(i: &'a str) -> PResult<&str, Call> {
    let (i, fn_name) = alt((
        |i: &'a str| {
            let (i, var_name) = parse_var
                .context("Variable used as a function name in a function call")
                .parse(i)?;
            Ok((i, FName::Var(var_name)))
        },
        |i: &'a str| {
            let (i, name) = many1(verify(anychar, |&c| c.is_alphanumeric() || c == '_'))
                .context("String literal used as a function name in a function call")
                .parse(i)?;
            Ok((i, FName::Literal(name.into_iter().collect())))
        },
    ))
    .parse(i)?;
    let (i, _) = char('(').parse(i)?;
    let (i, args) = parse_args1.context("Function call args").parse(i)?;
    let (i, _) = char(')').parse(i)?;
    Ok((i, Call { args, fn_name }))
}

fn parse_assignment(i: &str) -> PResult<&str, (VName, Expr)> {
    let (i, varname) = parse_var
        .context("Variable name in variable assignment")
        .parse(i)?;
    let (i, _) = multispace0.parse(i)?;
    let (i, _) = char('=')
        .context("Equality sign in variable assignment")
        .parse(i)?;
    let (i, _) = multispace0.parse(i)?;
    let (i, expr) = parse_expr
        .context("Right hand side expression in variable assignment")
        .parse(i)?;
    Ok((i, (varname, expr)))
}

fn parse_pval(i: &str) -> PResult<&str, PVal> {
    parse_var(i)
        .map(|(i, name)| (i, PVal::Var(name)))
        .or(parse_b64_string(i).map(|(i, val)| (i, PVal::StringLiteral(val))))
}

fn parse_expr(i: &str) -> PResult<&str, Expr> {
    alt((
        |i| {
            parse_call
                .context("Call expression")
                .parse(i)
                .map(|(i, call)| (i, Expr::Call(call)))
        },
        |i| {
            parse_pval
                .context("Value expression")
                .parse(i)
                .map(|(i, pval)| (i, Expr::Val(pval)))
        },
    ))
    .parse(i)
}

fn parse_eval(i: &str) -> PResult<&str, Expr> {
    let (i, _) = tag("eval").parse(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = char('(').parse(i)?;
    let (i, args) = parse_args1.context("Args in eval").parse(i)?;
    if args.len() != 1 {
        return fail
            .context("eval() call must have exactly one argument")
            .parse(i);
    }
    let (i, _) = char(')').context("Closing paren in eval").parse(i)?;
    // UNWRAP SAFETY: Checked args length == 1 in this function
    Ok((i, args[0].clone()))
}

fn parse_program(i: &str) -> PResult<&str, Program> {
    let (i, _) = multispace0.parse(i)?;
    let (i, maybe_assignment) = opt(parse_assignment
        .and(char(';'))
        .map(|(assignment, _)| assignment)
        .context("Variable assignment"))
    .parse(i)?;
    let (i, _) = multispace0.parse(i)?;
    let (i, eval_arg) = parse_eval.context("Final call to eval").parse(i)?;
    let (i, _) = char(';').parse(i)?;
    Ok((i, (maybe_assignment, eval_arg)))
}

fn parse(i: &str) -> Result<Program, ErrorTree<Location>> {
    final_parser(parse_program.context("Top-level program"))(i)
}

/// Program is an optional single variable assignment followed by an eval; eval takes a single argument of type Expr
type Program = (Option<(VName, Expr)>, Expr);

fn eval_expr(expr: Expr, env: &Env) -> Result<EVal> {
    match expr {
        Expr::Call(Call { fn_name, args }) => match fn_name {
            FName::Var(name) => {
                let fn_name = env
                    .get(&name)
                    .ok_or_else(|| {
                        anyhow!("Undefined variable used as a function name: {}", &name.0)
                    })
                    .cloned()?;
                match fn_name {
                    EVal::Text(name) => eval_expr(
                        Expr::Call(Call {
                            fn_name: FName::Literal(name),
                            args,
                        }),
                        env,
                    ),
                    EVal::Bytes(_) => Err(anyhow!("Function name must be expressed with a regular string, got a bytes representation instead")),
                }
            }
            FName::Literal(name) => match name.as_str() {
                "QNEXVV" => {
                    if args.len() != 2 {
                        return Err(anyhow!("QNEXVV is the XOR deobfuscation function and takes 2 arguments; got {} arguments instead", args.len()));
                    }
                    let args = args
                        .into_iter()
                        .map(|arg| eval_expr(arg, env))
                        .collect::<Result<Vec<EVal>>>()?;
                    let xor_output =
                        decode_with_xor(args[0].get_val_as_bytes(), &args[1].get_val_as_bytes())?;
                    Ok(EVal::Text(xor_output))
                }
                "base64_decode" => {
                    if args.len() != 1 {
                        return Err(anyhow!(
                            "base64_decode takes 1 argument; got {} arguments instead",
                            args.len()
                        ));
                    }
                    let args = args
                        .into_iter()
                        .map(|arg| eval_expr(arg, env))
                        .collect::<Result<Vec<EVal>>>()?;
                    let decode_output = base64_decode(&args[0].get_val_as_bytes())?;
                    Ok(EVal::Bytes(decode_output))
                }
                "strrev" => {
                    if args.len() != 1 {
                        return Err(anyhow!(
                            "strrev takes 1 argument; got {} arguments instead",
                            args.len()
                        ));
                    }
                    let args = args
                        .into_iter()
                        .map(|arg| eval_expr(arg, env))
                        .collect::<Result<Vec<EVal>>>()?;
                    let rev_output = args[0]
                        .get_val_as_bytes()
                        .as_ref()
                        .into_iter()
                        .rev()
                        .cloned()
                        .collect::<Vec<u8>>();
                    Ok(EVal::Bytes(rev_output))
                }
                "str_rot13" => {
                    if args.len() != 1 {
                        return Err(anyhow!(
                            "str_rot13 takes 1 argument; got {} arguments instead",
                            args.len()
                        ));
                    }
                    let args = args
                        .into_iter()
                        .map(|arg| eval_expr(arg, env))
                        .collect::<Result<Vec<EVal>>>()?;
                    let rot13_output = rot13(args[0].get_val_as_bytes().as_ref());
                    Ok(EVal::Bytes(rot13_output))
                }
                "gzuncompress" => {
                    if args.len() != 1 {
                        return Err(anyhow!(
                            "gzuncompress takes 1 argument; got {} arguments instead",
                            args.len()
                        ));
                    }
                    let args = args
                        .into_iter()
                        .map(|arg| eval_expr(arg, env))
                        .collect::<Result<Vec<EVal>>>()?;
                    let gzuncompress_output = gzuncompress(args[0].get_val_as_bytes().as_ref())?;
                    Ok(EVal::Text(gzuncompress_output))
                }
                _ => Err(anyhow!("Unknown function name: {}", name)),
            },
        },
        Expr::Val(PVal::Var(var_name)) => env
            .get(&var_name)
            .cloned()
            .ok_or_else(|| anyhow!("No variable named {}", var_name.0)),
        Expr::Val(PVal::StringLiteral(val)) => Ok(EVal::Text(val)),
    }
}

fn eval((maybe_assignment, eval_arg): Program, env: Env) -> Result<(EVal, Env)> {
    let env = if let Some((var_name, var_expr)) = maybe_assignment {
        let val = eval_expr(var_expr, &env)?;
        env.with(var_name, val)
    } else {
        env
    };
    let val = eval_expr(eval_arg, &env)?;
    Ok((val, env))
}

fn parse_and_eval(i: &str, env: Env) -> Result<(EVal, Env)> {
    let program = parse(i).context("Failed to parse program")?;
    eval(program, env)
}

fn deobfuscate(i: &str) -> Result<String> {
    let predefined_vars = vec![("PUMQXWZUDD", include_str!("PUMQXWZUDD.var"))];
    let env = Env::new()
        .with(
            VName("KAWSZFKWV".to_string()),
            EVal::Text("gzuncompress".to_string()),
        )
        .with(
            VName("MXTVB".to_string()),
            EVal::Text("base64_decode".to_string()),
        )
        .with_vars(predefined_vars);
    let mut count = 1;
    let (mut eval_call_arg, mut env) =
        parse_and_eval(i, env).context(format!("At {} call to parse and eval", count))?;
    loop {
        count += 1;
        let new_i = &eval_call_arg
            .get_text()
            .ok_or_else(|| anyhow!("Eval argument must evaluate to regular text, not bytes"))?;
        let (i, new_env) = parse_and_eval(new_i, env)
            .context(format!("At {} call to parse and eval", count))
            .context(new_i.to_string())?;
        env = new_env;
        eval_call_arg = i;
    }
}

fn rot13(input: &[u8]) -> Vec<u8> {
    input
        .iter()
        .map(|&c| match c {
            b'a'..=b'z' => (b'a' + (c - b'a' + 13) % 26),
            b'A'..=b'Z' => (b'A' + (c - b'A' + 13) % 26),
            _ => c,
        })
        .collect()
}

fn base64_decode<T: AsRef<[u8]>>(payload: T) -> Result<Vec<u8>> {
    let val = base64::engine::general_purpose::STANDARD.decode(payload)?;
    Ok(val)
}

fn base64_encode<T: AsRef<[u8]>>(payload: T) -> Result<String> {
    let val = base64::engine::general_purpose::STANDARD.encode(payload);
    Ok(val)
}

fn gzuncompress(bytes: &[u8]) -> Result<String> {
    let mut text = String::new();
    let mut decoder = ZlibDecoder::new(bytes);
    decoder.read_to_string(&mut text)?;
    Ok(text)
}

fn deob(payload: &str) -> Result<String> {
    let bytes = base64_decode(payload)?;
    gzuncompress(&bytes)
}

const FUNCS: [&str; 31] = [
    "7068705F756E616D65",
    "73657373696F6E5F7374617274",
    "6572726F725F7265706F7274696E67",
    "70687076657273696F6E",
    "66696C655F7075745F636F6E74656E7473",
    "66696C655F6765745F636F6E74656E7473",
    "66696C657065726D73",
    "66696C656D74696D65",
    "66696C6574797065",
    "68746D6C7370656369616C6368617273",
    "737072696E7466",
    "737562737472",
    "676574637764",
    "6368646972",
    "7374725F7265706C616365",
    "6578706C6F6465",
    "666C617368",
    "6D6F76655F75706C6F616465645F66696C65",
    "7363616E646972",
    "676574686F737462796E616D65",
    "7368656C6C5F65786563",
    "74727565",
    "6469726E616D65",
    "64617465",
    "6D696D655F636F6E74656E745F74797065",
    "66756E6374696F6E5F657869737473",
    "6673697A65",
    "726D646972",
    "756E6C696E6B",
    "6D6B646972",
    "72656E616D65",
];

fn main() {
    for (idx, func_encoded) in FUNCS.into_iter().enumerate() {
        let mut func_decoded = String::new();
        for (i, _) in func_encoded.char_indices().step_by(2) {
            let ch = &func_encoded[i..i + 2];
            let decoded_ch: char = u32::from_str_radix(ch, 16).unwrap().try_into().unwrap();
            func_decoded += &decoded_ch.to_string();
        }
        println!("Function {}: {}", idx, func_decoded);
    }
    // let input = include_str!("main.in");
    // let result = deobfuscate(input).unwrap();
    // println!("RESULT: {:#?}", result);
}

#[cfg(test)]
mod tests {
    use anyhow::Context;
    use nom_supreme::{
        error::ErrorTree,
        final_parser::{final_parser, Location},
    };

    use crate::{parse, parse_and_eval, parse_args1, parse_eval, EVal, Env, Expr, FName, VName};

    #[test]
    fn basic_parse() {
        let eval_program = include_str!("test1.in");
        let expected_decoded_text = include_str!("test1.out");

        let env = Env::new()
            .with(
                VName("KAWSZFKWV".to_string()),
                EVal::Text("gzuncompress".to_string()),
            )
            .with(
                VName("MXTVB".to_string()),
                EVal::Text("base64_decode".to_string()),
            );
        let (EVal::Text(hex), _) = parse_and_eval(&eval_program, env).unwrap() else {
            panic!();
        };
        assert_eq!(expected_decoded_text.to_string(), hex);
    }

    #[test]
    fn parse_with_obfuscation() {
        let eval_program = include_str!("test2.in");

        let expected_decoded_program = include_str!("test2.out");
        let env = Env::new()
            .with(
                VName("KAWSZFKWV".to_string()),
                EVal::Text("gzuncompress".to_string()),
            )
            .with(
                VName("MXTVB".to_string()),
                EVal::Text("base64_decode".to_string()),
            );
        let (EVal::Text(hex), _) = parse_and_eval(&eval_program, env).unwrap() else {
            panic!();
        };
        assert_eq!(expected_decoded_program.to_string(), hex);
    }

    #[test]
    fn parse_ambiguous() {
        let eval_program = include_str!("test3.in");
        let expected_decoded_program = include_str!("test3.out");

        let env = Env::new()
            .with(
                VName("KAWSZFKWV".to_string()),
                EVal::Text("gzuncompress".to_string()),
            )
            .with(
                VName("MXTVB".to_string()),
                EVal::Text("base64_decode".to_string()),
            );
        let (EVal::Text(hex), _) = parse_and_eval(&eval_program, env).unwrap() else {
            panic!();
        };
        assert_eq!(expected_decoded_program.to_string(), hex);
    }

    #[test]
    fn parse_args() {
        let args = "$ABC, 'Aw2+=/'";
        assert_eq!(
            vec![
                Expr::Val(crate::PVal::Var(VName::from("ABC"))),
                Expr::Val(crate::PVal::StringLiteral("Aw2+=/".to_string()))
            ],
            final_parser::<_, _, _, ErrorTree<Location>>(parse_args1)(args)
                .context("top-level")
                .unwrap()
        );
    }

    #[test]
    fn parse_args_nested_call() {
        let args = "abc(\'A1+=\')";
        assert_eq!(
            vec![Expr::Call(crate::Call {
                fn_name: FName::Literal("abc".to_string()),
                args: vec![Expr::Val(crate::PVal::StringLiteral("A1+=".to_string()))]
            }),],
            final_parser::<_, _, _, ErrorTree<Location>>(parse_args1)(args)
                .context("top-level")
                .unwrap()
        );
    }

    #[test]
    fn parse_call_with_underscores() {
        let args = "abc_def(\'A1+=\')";
        assert_eq!(
            vec![Expr::Call(crate::Call {
                fn_name: FName::Literal("abc_def".to_string()),
                args: vec![Expr::Val(crate::PVal::StringLiteral("A1+=".to_string()))]
            }),],
            final_parser::<_, _, _, ErrorTree<Location>>(parse_args1)(args)
                .context("top-level")
                .unwrap()
        );
    }

    #[test]
    fn parse_args_multiple_nested_calls() {
        let args = "ghi(def(abc(\'A1+=\')))";
        assert_eq!(
            vec![Expr::Call(crate::Call {
                fn_name: FName::Literal("ghi".to_string()),
                args: vec![Expr::Call(crate::Call {
                    fn_name: FName::Literal("def".to_string()),
                    args: vec![Expr::Call(crate::Call {
                        fn_name: FName::Literal("abc".to_string()),
                        args: vec![Expr::Val(crate::PVal::StringLiteral("A1+=".to_string()))]
                    }),]
                })]
            })],
            final_parser::<_, _, _, ErrorTree<Location>>(parse_args1)(args)
                .context("top-level")
                .unwrap()
        );
    }

    #[test]
    fn parse_args_multiple_nested_calls_with_variable_names() {
        let args = "$GHI(def($ABC(\'A1+=\')))";
        assert_eq!(
            vec![Expr::Call(crate::Call {
                fn_name: FName::Var(VName::from("GHI")),
                args: vec![Expr::Call(crate::Call {
                    fn_name: FName::Literal("def".to_string()),
                    args: vec![Expr::Call(crate::Call {
                        fn_name: FName::Var(VName::from("ABC")),
                        args: vec![Expr::Val(crate::PVal::StringLiteral("A1+=".to_string()))]
                    }),]
                })]
            })],
            final_parser::<_, _, _, ErrorTree<Location>>(parse_args1)(args)
                .context("top-level")
                .unwrap()
        );
    }

    #[test]
    fn parse_eval_multiple_nested_calls_with_variable_names() {
        let eval_expr = "eval($GHI(def($ABC(\'A1+=\'))))";
        assert_eq!(
            Expr::Call(crate::Call {
                fn_name: FName::Var(VName::from("GHI")),
                args: vec![Expr::Call(crate::Call {
                    fn_name: FName::Literal("def".to_string()),
                    args: vec![Expr::Call(crate::Call {
                        fn_name: FName::Var(VName::from("ABC")),
                        args: vec![Expr::Val(crate::PVal::StringLiteral("A1+=".to_string()))]
                    }),]
                })]
            }),
            final_parser::<_, _, _, ErrorTree<Location>>(parse_eval)(eval_expr)
                .context("top-level")
                .unwrap()
        );
    }

    #[test]
    fn parse_program_eval_multiple_nested_calls_with_variable_names() {
        let eval_expr = "eval($GHI(def($ABC(\'A1+=\'))));";
        assert_eq!(
            (
                None,
                Expr::Call(crate::Call {
                    fn_name: FName::Var(VName::from("GHI")),
                    args: vec![Expr::Call(crate::Call {
                        fn_name: FName::Literal("def".to_string()),
                        args: vec![Expr::Call(crate::Call {
                            fn_name: FName::Var(VName::from("ABC")),
                            args: vec![Expr::Val(crate::PVal::StringLiteral("A1+=".to_string()))]
                        }),]
                    })]
                })
            ),
            parse(eval_expr).context("top-level").unwrap()
        );
    }
}
