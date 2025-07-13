# wgsl-macro

A modular and async-capable preprocessor for WGSL (WebGPU Shading Language) shader source files.\
Supports powerful directives like `#import`, `#ifdef`, `#const`, and conditionals to enable reusable, compile-time evaluated shader logic.

> **Use this crate to modularize your WGSL code, inject constants, and evaluate conditions in shaders before compilation.**

---

## ✨ Features

- `#import` other shader modules by path or scheme (e.g. `embedded://...`)
- `#const` injection for compile-time constants
- `#if`, `#ifdef`, `#ifndef`, `#else`, `#end` logic blocks
- Nested and multi-branch conditional support
- Async import resolution (ideal for Web/WebGPU environments)
- Strong error handling and detailed diagnostics

---

## 📆 Installation

Add to your `Cargo.toml`:

```toml
wgsl-macro = "0.1"
```

---

## 🧪 Example

```rust
use wgsl_preprocessor::{ShaderProcessor, ShaderConstant, ShaderConstants};

let mut processor = ShaderProcessor::new();
processor.add_module("embedded://shaders/utils.wgsl", "fn util() {}");

let mut constants = ShaderConstants::new();
constants.set("LIGHT_COUNT", ShaderConstant::U32(50));

let source = r#"
    #import embedded://shaders/utils.wgsl
    const LIGHT_COUNT: u32 = 10;
    #if LIGHT_COUNT == 50
        fn main() {
            util();
        }
    #end
"#;

let result = processor.build(source, &constants).unwrap();
println!("{}", result);
```

---

## 🔧 Supported Directives

- `#import path` – Load another module by path
- `#const NAME: TYPE = VALUE;` – Define constants
- `#if`, `#else if`, `#else`, `#end` – Conditional logic
- `#ifdef`, `#ifndef` – Check if constants exist

---

## 🌐 Async Imports

You can collect all `#import` directives asynchronously using `get_imports`:

```rust
use wgsl_preprocessor::ShaderProcessor;

let imports = ShaderProcessor::get_imports(shader_src, |path| async move {
    // Fetch from disk, server, or embedded assets
    Ok(load_shader_from_source(path))
}).await?;
```

---

## 🚧 Roadmap

- Expression parser for more advanced constant evaluation
- GLSL support
- CLI tool for shader preprocessing

---

## 📄 License

Licensed under MIT or Apache-2.0 (your choice).

---

## ❤️ Contributions

PRs, issues, and suggestions are welcome! Whether you want to support `#define`-style macros, improve error reporting, or just fix typos — contributions are appreciated!

