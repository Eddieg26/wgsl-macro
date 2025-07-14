use std::{
    borrow::Cow,
    collections::{HashMap, HashSet, VecDeque},
    error::Error,
    fmt::Display,
    pin::Pin,
};

#[derive(Debug)]
pub enum ShaderProcessorError<'a> {
    /// An `#import` path could not be found in the context.
    MissingImport { path: &'a str },

    /// A required constant was referenced but not defined.
    UndefinedConstant { name: &'a str },

    /// Failed to parse or evaluate a constant expression.
    InvalidCondition { expression: &'a str },

    /// An else block was encountered without a preceding `#if` or `#ifdef`.
    UnmatchedElse { line: &'a str },

    /// A block opened (e.g., with `#if`) but never closed properly with `#end`.
    UnclosedConditional { line: &'a str },

    /// A `#const` line couldn't be parsed correctly.
    InvalidConstSyntax { line: &'a str },

    /// Internal error due to malformed input or iterator exhaustion.
    UnexpectedEndOfInput,

    /// Generic error with context.
    Message(Cow<'a, str>),
}

impl<'a> Display for ShaderProcessorError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ShaderProcessorError::MissingImport { path } => {
                write!(f, "Missing import: {}", path)
            }
            ShaderProcessorError::UndefinedConstant { name } => {
                write!(f, "Undefined constant: {}", name)
            }
            ShaderProcessorError::InvalidCondition { expression } => {
                write!(f, "Invalid condition expression: {}", expression)
            }
            ShaderProcessorError::UnmatchedElse { line } => {
                write!(f, "Unmatched else block at: {}", line)
            }
            ShaderProcessorError::UnclosedConditional { line } => {
                write!(f, "Unclosed conditional block at: {}", line)
            }
            ShaderProcessorError::InvalidConstSyntax { line } => {
                write!(f, "Invalid const syntax in line: {}", line)
            }
            ShaderProcessorError::UnexpectedEndOfInput => {
                write!(f, "Unexpected end of input")
            }
            ShaderProcessorError::Message(msg) => {
                write!(f, "{}", msg)
            }
        }
    }
}

impl<'a> From<&'a str> for ShaderProcessorError<'a> {
    fn from(value: &'a str) -> Self {
        Self::Message(Cow::from(value))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ShaderConstant {
    Bool(bool),
    I32(i32),
    U32(u32),
}

impl ShaderConstant {
    fn equals<'a>(&self, value: &'a str) -> Result<bool, ShaderProcessorError<'a>> {
        match self {
            ShaderConstant::Bool(v) => {
                if let Ok(b) = value.parse::<bool>() {
                    Ok(*v == b)
                } else {
                    Err(ShaderProcessorError::InvalidCondition { expression: value })
                }
            }
            ShaderConstant::I32(v) => value
                .parse::<i32>()
                .map(|i| *v == i)
                .map_err(|_| ShaderProcessorError::InvalidCondition { expression: value }),
            ShaderConstant::U32(v) => value
                .parse::<u32>()
                .map(|u| *v == u)
                .map_err(|_| ShaderProcessorError::InvalidCondition { expression: value }),
        }
    }

    fn greater_than<'a>(&self, value: &'a str) -> Result<bool, ShaderProcessorError<'a>> {
        match self {
            ShaderConstant::I32(v) => value
                .parse::<i32>()
                .ok()
                .map(|i| *v > i)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            ShaderConstant::U32(v) => value
                .parse::<u32>()
                .ok()
                .map(|u| *v > u)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            _ => Err(ShaderProcessorError::InvalidCondition { expression: value }),
        }
    }

    fn less_than<'a>(&self, value: &'a str) -> Result<bool, ShaderProcessorError<'a>> {
        match self {
            ShaderConstant::I32(v) => value
                .parse::<i32>()
                .ok()
                .map(|i| *v < i)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            ShaderConstant::U32(v) => value
                .parse::<u32>()
                .ok()
                .map(|u| *v < u)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            _ => Err(ShaderProcessorError::InvalidCondition { expression: value }),
        }
    }

    fn greater_than_or_equal<'a>(&self, value: &'a str) -> Result<bool, ShaderProcessorError<'a>> {
        match self {
            ShaderConstant::I32(v) => value
                .parse::<i32>()
                .ok()
                .map(|i| *v >= i)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            ShaderConstant::U32(v) => value
                .parse::<u32>()
                .ok()
                .map(|u| *v >= u)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            _ => Err(ShaderProcessorError::InvalidCondition { expression: value }),
        }
    }

    fn less_than_or_equal<'a>(&self, value: &'a str) -> Result<bool, ShaderProcessorError<'a>> {
        match self {
            ShaderConstant::I32(v) => value
                .parse::<i32>()
                .ok()
                .map(|i| *v <= i)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            ShaderConstant::U32(v) => value
                .parse::<u32>()
                .ok()
                .map(|u| *v <= u)
                .ok_or(ShaderProcessorError::InvalidCondition { expression: value }),
            _ => Err(ShaderProcessorError::InvalidCondition { expression: value }),
        }
    }
}

impl ToString for ShaderConstant {
    fn to_string(&self) -> String {
        match self {
            ShaderConstant::Bool(v) => v.to_string(),
            ShaderConstant::I32(v) => v.to_string(),
            ShaderConstant::U32(v) => v.to_string(),
        }
    }
}

#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ShaderConstants(HashMap<String, ShaderConstant>);
impl ShaderConstants {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn contains(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }

    pub fn get(&self, name: &str) -> Option<ShaderConstant> {
        self.0.get(name).copied()
    }

    pub fn set(&mut self, name: impl ToString, value: ShaderConstant) {
        self.0.insert(name.to_string(), value);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&String, &ShaderConstant)> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }
}

impl From<HashMap<String, ShaderConstant>> for ShaderConstants {
    fn from(value: HashMap<String, ShaderConstant>) -> Self {
        Self(value)
    }
}

pub type ShaderImports = HashMap<String, String>;

pub enum Token<'a> {
    /// #import embedded://shaders/utils.wgsl
    Import(&'a str),
    /// const LIGHT_COUNT: u32 = 50;
    Const(&'a str),
    /// #if LIGHT_COUNT == 50
    If(&'a str),
    /// #ifdef LIGHT_COUNT
    IfDef(&'a str),
    /// #ifndef LIGHT_COUNT
    IfNotDef(&'a str),
    /// #end
    EndIf(&'a str),
    /// #else
    Else(&'a str),
    /// #else if
    ElseIf(&'a str),
    /// #else ifdef
    ElseIfDef(&'a str),
    Chars(&'a str),
}

impl Token<'_> {
    const IMPORT: &'static str = "#import";
    const CONST: &'static str = "const ";
    const IF: &'static str = "#if ";
    const IFDEF: &'static str = "#ifdef ";
    const IFNDEF: &'static str = "#ifndef ";
    const ELSE: &'static str = "#else";
    const ELSE_IF: &'static str = "#else if ";
    const ELSE_IFDEF: &'static str = "#else ifdef ";
    const ENDIF: &'static str = "#end";
}

pub struct BranchBlock<'a> {
    line: &'a str,
    eval:
        Option<for<'b> fn(&'b str, &'b ShaderConstants) -> Result<bool, ShaderProcessorError<'b>>>,
    tokens: Vec<Token<'a>>,
}

impl<'a> BranchBlock<'a> {
    pub fn new(line: &'a str) -> Self {
        Self {
            line,
            eval: None,
            tokens: Vec::new(),
        }
    }

    pub fn with(
        line: &'a str,
        eval: for<'b> fn(&'b str, &'b ShaderConstants) -> Result<bool, ShaderProcessorError<'b>>,
    ) -> Self {
        Self {
            line,
            eval: Some(eval),
            tokens: Vec::new(),
        }
    }
}

pub struct ShaderProcessor<'a> {
    modules: HashMap<&'a str, &'a str>,
    processed: HashSet<&'a str>,
}

pub type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

impl<'a> ShaderProcessor<'a> {
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
            processed: HashSet::new(),
        }
    }

    pub fn add_module(&mut self, path: &'a str, module: &'a str) {
        self.modules.insert(path, module);
    }

    pub fn build(
        &mut self,
        src: &'a str,
        constants: &'a ShaderConstants,
    ) -> Result<String, ShaderProcessorError<'a>> {
        let mut tokens = Self::tokenize(src);

        self.process_tokens(&mut tokens, constants)
    }

    pub async fn get_imports<F, E, Ctx>(
        src: &'a str,
        ctx: &'a Ctx,
        resolve: impl Fn(String, &'a Ctx) -> F,
    ) -> Result<ShaderImports, ShaderProcessorError<'a>>
    where
        E: Error,
        F: Future<Output = Result<String, E>>,
    {
        let mut imports = ShaderImports::new();
        let mut sources = VecDeque::new();
        sources.push_front(Cow::Borrowed(src));

        while let Some(src) = sources.pop_front() {
            for token in ShaderProcessor::tokenize(&src) {
                if let Token::Import(line) = token {
                    let path = match ShaderProcessor::parse_import(line) {
                        Ok(path) => path,
                        Err(e) => {
                            return Err(ShaderProcessorError::Message(e.to_string().into()));
                        }
                    };

                    if imports.contains_key(path) {
                        continue;
                    }

                    // Resolve the import asynchronously
                    let source = match resolve(path.trim().to_string(), ctx).await {
                        Ok(source) => source,
                        Err(e) => {
                            return Err(ShaderProcessorError::Message(e.to_string().into()));
                        }
                    };

                    imports.insert(path.to_string(), source.clone());
                    sources.push_back(Cow::Owned(source));
                }
            }
        }

        Ok(imports)
    }

    fn tokenize(src: &str) -> impl Iterator<Item = Token<'_>> {
        src.lines().map(|line| {
            let trimmed = line.trim_start();

            if trimmed.starts_with(Token::IMPORT) {
                Token::Import(trimmed)
            } else if trimmed.starts_with(Token::CONST) {
                Token::Const(line)
            } else if trimmed.starts_with(Token::IF) {
                Token::If(trimmed)
            } else if trimmed.starts_with(Token::IFDEF) {
                Token::IfDef(trimmed)
            } else if trimmed.starts_with(Token::IFNDEF) {
                Token::IfNotDef(trimmed)
            } else if trimmed.starts_with(Token::ELSE_IFDEF) {
                Token::ElseIfDef(trimmed)
            } else if trimmed.starts_with(Token::ELSE_IF) {
                Token::ElseIf(trimmed)
            } else if trimmed.starts_with(Token::ELSE) {
                Token::Else(trimmed)
            } else if trimmed.starts_with(Token::ENDIF) {
                Token::EndIf(trimmed)
            } else {
                Token::Chars(line)
            }
        })
    }

    fn process_tokens(
        &mut self,
        tokens: &mut impl Iterator<Item = Token<'a>>,
        constants: &'a ShaderConstants,
    ) -> Result<String, ShaderProcessorError<'a>> {
        let mut code = String::new();

        while let Some(token) = tokens.next() {
            match token {
                Token::Import(line) => {
                    let path = Self::parse_import(line)?.trim();

                    if !self.processed.contains(path) {
                        let src = self
                            .modules
                            .get(path)
                            .ok_or(ShaderProcessorError::MissingImport { path })?;

                        let module = self.build(src, constants)?;
                        code.push_str(&module);
                        self.processed.insert(path);
                    }
                }
                Token::Const(line) => {
                    let start = line.split_whitespace().next().unwrap_or("");
                    let trimmed = line.trim_start();
                    let name_end = trimmed
                        .find(":")
                        .ok_or(ShaderProcessorError::InvalidConstSyntax { line })?;
                    let name = trimmed
                        .get(Token::CONST.len()..name_end)
                        .ok_or(ShaderProcessorError::InvalidConstSyntax { line })?
                        .trim();
                    let ty = trimmed
                        .get(name_end + 1..)
                        .ok_or(ShaderProcessorError::InvalidConstSyntax { line })?
                        .split("=")
                        .next()
                        .ok_or(ShaderProcessorError::InvalidConstSyntax { line })?
                        .trim();
                    let value = constants
                        .get(name)
                        .ok_or(ShaderProcessorError::InvalidConstSyntax { line })?
                        .to_string();
                    code.push_str(&format!("{start} {name}: {ty} = {value};"));
                    code.push('\n');
                }
                Token::If(line) => {
                    let condition = line
                        .get(Token::IF.len()..)
                        .ok_or(ShaderProcessorError::InvalidCondition { expression: line })?
                        .trim();
                    let blocks = self.collect_branch_blocks(
                        tokens,
                        BranchBlock::with(condition, Self::eval_condition),
                    )?;
                    code.push_str(&self.process_branch_blocks(blocks, constants)?);
                }
                Token::IfDef(line) => {
                    let condition = line
                        .get(Token::IF.len()..)
                        .ok_or(ShaderProcessorError::InvalidCondition { expression: line })?
                        .trim();
                    let eval =
                        |name: &str, constants: &ShaderConstants| Ok(constants.contains(name));
                    let blocks =
                        self.collect_branch_blocks(tokens, BranchBlock::with(condition, eval))?;
                    code.push_str(&self.process_branch_blocks(blocks, constants)?);
                }
                Token::IfNotDef(line) => {
                    let condition = line
                        .get(Token::IF.len()..)
                        .ok_or(ShaderProcessorError::InvalidCondition { expression: line })?
                        .trim();
                    let eval =
                        |name: &str, constants: &ShaderConstants| Ok(!constants.contains(name));
                    let blocks =
                        self.collect_branch_blocks(tokens, BranchBlock::with(condition, eval))?;
                    code.push_str(&self.process_branch_blocks(blocks, constants)?);
                }
                Token::Chars(line) => {
                    code.push_str(line);
                    code.push('\n');
                }
                Token::EndIf(line) => {
                    return Err(ShaderProcessorError::UnclosedConditional { line });
                }
                Token::Else(line) => return Err(ShaderProcessorError::UnmatchedElse { line }),
                Token::ElseIf(line) => {
                    return Err(ShaderProcessorError::UnmatchedElse { line });
                }
                Token::ElseIfDef(line) => {
                    return Err(ShaderProcessorError::UnmatchedElse { line });
                }
            }
        }

        Ok(code)
    }

    fn collect_branch_blocks(
        &self,
        tokens: &mut impl Iterator<Item = Token<'a>>,
        current: BranchBlock<'a>,
    ) -> Result<Vec<BranchBlock<'a>>, ShaderProcessorError<'a>> {
        let mut blocks = Vec::new();
        let mut current = Some(current);

        while let Some(token) = tokens.next() {
            match token {
                Token::ElseIf(line) => {
                    blocks.extend(current.take());
                    let condition = line
                        .get(Token::ELSE_IF.len()..)
                        .ok_or(ShaderProcessorError::InvalidCondition { expression: line })?;

                    current = Some(BranchBlock::with(condition, Self::eval_condition))
                }
                Token::Else(line) => {
                    blocks.extend(current.take());
                    current = Some(BranchBlock::new(line));
                }
                Token::ElseIfDef(line) => {
                    blocks.extend(current.take());
                    let condition = line
                        .get(Token::ELSE.len()..)
                        .ok_or(ShaderProcessorError::InvalidCondition { expression: line })?
                        .trim();
                    let eval =
                        |name: &str, constants: &ShaderConstants| Ok(constants.contains(name));

                    current = Some(BranchBlock::with(condition, eval))
                }
                Token::EndIf(_) => {
                    blocks.extend(current);
                    break;
                }
                _ => current
                    .as_mut()
                    .ok_or(ShaderProcessorError::UnexpectedEndOfInput)?
                    .tokens
                    .push(token),
            }
        }

        Ok(blocks)
    }

    fn process_branch_blocks(
        &mut self,
        blocks: Vec<BranchBlock<'a>>,
        constants: &'a ShaderConstants,
    ) -> Result<String, ShaderProcessorError<'a>> {
        for block in blocks {
            let Some(result) = block.eval.map(|f| f(block.line, constants)) else {
                continue;
            };

            match result {
                Ok(false) => continue,
                Ok(true) => {
                    return self.process_tokens(&mut block.tokens.into_iter(), constants);
                }
                Err(err) => return Err(err),
            }
        }

        Err(ShaderProcessorError::UnmatchedElse {
            line: "No matching condition found for else block",
        })
    }

    fn eval_condition<'b>(
        condition: &'b str,
        constants: &'b ShaderConstants,
    ) -> Result<bool, ShaderProcessorError<'b>> {
        let parse = |pos: usize| -> Option<(&str, ShaderConstant)> {
            let name = condition.get(..pos)?.trim();
            let value = condition.get(pos + 2..)?.trim();
            let constant = constants.get(name)?;

            Some((value, constant))
        };

        if let Some(pos) = condition.find("==") {
            let (value, constant) = parse(pos).ok_or(ShaderProcessorError::InvalidCondition {
                expression: condition,
            })?;
            constant.equals(value)
        } else if let Some(pos) = condition.find("!=") {
            let (value, constant) = parse(pos).ok_or(ShaderProcessorError::InvalidCondition {
                expression: condition,
            })?;
            constant.equals(value).map(|v| !v)
        } else if let Some(pos) = condition.find(">=") {
            let (value, constant) = parse(pos).ok_or(ShaderProcessorError::InvalidCondition {
                expression: condition,
            })?;
            constant.greater_than_or_equal(value)
        } else if let Some(pos) = condition.find("<=") {
            let (value, constant) = parse(pos).ok_or(ShaderProcessorError::InvalidCondition {
                expression: condition,
            })?;
            constant.less_than_or_equal(value)
        } else if let Some(pos) = condition.find(">") {
            let (value, constant) = parse(pos).ok_or(ShaderProcessorError::InvalidCondition {
                expression: condition,
            })?;
            constant.greater_than(value)
        } else if let Some(pos) = condition.find("<") {
            let (value, constant) = parse(pos).ok_or(ShaderProcessorError::InvalidCondition {
                expression: condition,
            })?;
            constant.less_than(value)
        } else {
            Err(ShaderProcessorError::InvalidCondition {
                expression: condition,
            })
        }
    }

    fn parse_import(line: &str) -> Result<&str, ShaderProcessorError<'_>> {
        line.get(Token::IMPORT.len()..)
            .ok_or(ShaderProcessorError::from("Failed to parse import path"))
    }
}

#[allow(unused_imports)]
mod tests {
    use std::collections::HashMap;

    use crate::{ShaderConstant, ShaderConstants, ShaderProcessor};

    #[test]
    fn test_shader_processor() {
        // Example test case for ShaderProcessor
        let mut processor = ShaderProcessor::new();
        processor.add_module("embedded://shaders/utils.wgsl", "fn util() {}");

        let mut constants = ShaderConstants::new();
        constants.set("LIGHT_COUNT", ShaderConstant::U32(50));

        let src = r#"
            #import embedded://shaders/utils.wgsl
            const LIGHT_COUNT: u32 = 10;
            #if LIGHT_COUNT == 50
                fn main() {
                    util();
                }
            #end
        "#;

        let expected = r#"
            fn util() {}
const LIGHT_COUNT: u32 = 50;
                fn main() {
                    util();
                }
        "#;

        let result = processor.build(src, &constants).unwrap();
        assert_eq!(result.trim(), expected.trim());
    }

    #[test]
    fn test_nested_imports() {
        // Example test case for nested imports
        let mut processor = ShaderProcessor::new();
        processor.add_module("embedded://shaders/utils.wgsl", "fn util() {}");
        processor.add_module(
            "embedded://shaders/nested.wgsl",
            "#import embedded://shaders/utils.wgsl\nfn nested() {}",
        );

        let mut constants = ShaderConstants::new();
        constants.set("LIGHT_COUNT", ShaderConstant::U32(50));

        let src = r#"
            #import embedded://shaders/nested.wgsl
            const LIGHT_COUNT: u32 = 50;
            #if LIGHT_COUNT == 50
                fn main() {
                    util();
                    nested();
                }
            #end
        "#;

        let expected = r#"
            fn util() {}
fn nested() {}
const LIGHT_COUNT: u32 = 50;
                fn main() {
                    util();
                    nested();
                }
        "#;

        let result = processor.build(src, &constants).unwrap();
        assert_eq!(result.trim(), expected.trim());
    }

    #[test]
    fn test_get_imports() {
        let mut imports = HashMap::new();
        imports.insert("embedded://shaders/utils.wgsl", "utils");
        imports.insert("embedded://shaders/nested.wgsl", "nested");
        imports.insert("embedded://shaders/another.wgsl", "another");

        let src = r#"
            #import embedded://shaders/utils.wgsl
            #import embedded://shaders/nested.wgsl
            #import embedded://shaders/another.wgsl
        "#;

        let result = pollster::block_on(ShaderProcessor::get_imports(
            src,
            &imports,
            |path: String, imports| async move {
                imports
                    .get(path.as_str())
                    .map(|v| v.to_string())
                    .ok_or(std::io::Error::from(std::io::ErrorKind::NotFound))
            },
        ))
        .unwrap();

        assert_eq!(imports.len(), result.len());
        let collected_all = result
            .iter()
            .all(|(path, value)| result.get(path.as_str()).unwrap() == value);

        assert!(collected_all);
    }
}
