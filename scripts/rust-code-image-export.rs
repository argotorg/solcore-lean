//! Exact linked section bytes and symbol extents from the pinned Sonatina backend.
//! Input is the same checked program's Hull JSON and printed Sonatina IR.
//! This executable performs compilation only; it never executes EVM instructions.

use serde_json::{json, Value};
use sonatina_codegen::{
    object::{ObjectArtifact, SymbolId},
    EvmCompile, OptLevel,
};
use std::{env, fmt::Write, fs};

const UPSTREAM: &str = "2a745e12974c373c3799fec81b48a53c7dce2ab4";
const BACKEND: &str = "8ee24814ea9b32c762df8ef80c796e7d48797c0f";

fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str, String> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("missing string {key}"))
}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(2 + bytes.len() * 2);
    result.push_str("0x");
    for byte in bytes {
        write!(result, "{byte:02x}").expect("string write");
    }
    result
}

// Same injective section naming as solcore-sonatina lower.rs. Section existence
// and all immediate embed names/bytes are checked against backend artifacts.
fn section_name(scope: &str) -> String {
    let mut encoded = format!("{}_", scope.len());
    for byte in scope.bytes() {
        if byte.is_ascii_alphanumeric() {
            encoded.push(char::from(byte));
        } else {
            write!(encoded, "_{byte:02x}").expect("string write");
        }
    }
    format!("solcore_object_{encoded}")
}

fn image(
    object: &Value,
    scope: &str,
    parent: &[String],
    section_name: &str,
    artifact: &ObjectArtifact,
    images: &mut Vec<Value>,
) -> Result<(), String> {
    let name = string(object, "name")?;
    let mut path = parent.to_vec();
    path.push(name.to_owned());
    let section = artifact
        .sections
        .iter()
        .find(|(key, _)| key.0.as_str() == section_name)
        .map(|(_, value)| value)
        .ok_or_else(|| format!("missing section {section_name}"))?;
    let current = section
        .symtab
        .get(&SymbolId::CurrentSection)
        .ok_or("backend omitted current-section linker extent")?;
    if current.offset != 0 || current.size as usize != section.bytes.len() {
        return Err("current-section extent disagrees with actual bytes".into());
    }
    let children = object
        .get("inners")
        .and_then(Value::as_array)
        .ok_or("missing Hull inners")?;
    let mut embeds = Vec::new();
    for (symbol, extent) in &section.symtab {
        if let SymbolId::Embed(symbol) = symbol {
            if !children
                .iter()
                .any(|child| child.get("name").and_then(Value::as_str) == Some(symbol.0.as_str()))
            {
                return Err(format!(
                    "backend embed {} has no direct Hull child",
                    symbol.0
                ));
            }
            embeds.push(
                json!({"name":symbol.0.as_str(), "offset":extent.offset, "size":extent.size}),
            );
        }
    }
    embeds.sort_by(|left, right| left["name"].as_str().cmp(&right["name"].as_str()));
    if embeds.len() != children.len() {
        return Err("backend embed inventory differs from Hull".into());
    }
    images.push(json!({"path":path, "bytes":hex(&section.bytes), "embeds":embeds}));
    for (index, child) in children.iter().enumerate() {
        let child_scope = format!("{scope}.inner{index}");
        let child_section = if parent.is_empty() && index == 0 {
            "runtime".to_owned()
        } else {
            self::section_name(&child_scope)
        };
        let child_name = string(child, "name")?;
        let extent = section
            .symtab
            .iter()
            .find_map(|(symbol, extent)| match symbol {
                SymbolId::Embed(symbol) if symbol.0.as_str() == child_name => Some(extent),
                _ => None,
            })
            .ok_or_else(|| format!("missing child symbol {child_name}"))?;
        let child_bytes = &artifact
            .sections
            .iter()
            .find(|(key, _)| key.0.as_str() == child_section)
            .map(|(_, value)| value)
            .ok_or_else(|| format!("missing child section {child_section}"))?
            .bytes;
        let begin = extent.offset as usize;
        let end = begin
            .checked_add(extent.size as usize)
            .ok_or("embed range overflow")?;
        if extent.size as usize != child_bytes.len()
            || section.bytes.get(begin..end) != Some(child_bytes.as_slice())
        {
            return Err(format!("embedded bytes differ from child {child_name}"));
        }
        image(child, &child_scope, &path, &child_section, artifact, images)?;
    }
    Ok(())
}

// Hull expressions routinely exceed serde_json's default depth of 128. Keep
// an explicit transport bound while parsing on the existing 64 MiB worker stack.
fn hull_json(source: &str) -> Result<Value, String> {
    const MAX_DEPTH: usize = 4096;
    const MAX_BYTES: usize = 128 * 1024 * 1024;
    if source.len() > MAX_BYTES {
        return Err("Hull JSON exceeds 128 MiB transport limit".into());
    }
    let (mut depth, mut quoted, mut escaped) = (0usize, false, false);
    for byte in source.bytes() {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'[' | b'{' => {
                    depth += 1;
                    if depth > MAX_DEPTH {
                        return Err("Hull JSON exceeds depth limit 4096".into());
                    }
                }
                b']' | b'}' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    let mut decoder = serde_json::Deserializer::from_str(source);
    decoder.disable_recursion_limit();
    let mut values = decoder.into_iter::<Value>();
    let value = values
        .next()
        .ok_or("empty Hull JSON")?
        .map_err(|error| error.to_string())?;
    if values.next().is_some() {
        return Err("trailing Hull JSON input".into());
    }
    Ok(value)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Optimization {
    O0,
    O2,
}

impl Optimization {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "O0" => Ok(Self::O0),
            "O2" => Ok(Self::O2),
            _ => Err(format!(
                "unsupported optimization {value}; expected O0 or O2"
            )),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::O0 => "O0",
            Self::O2 => "O2",
        }
    }

    fn level(self) -> OptLevel {
        match self {
            Self::O0 => OptLevel::O0,
            Self::O2 => OptLevel::O2,
        }
    }
}

fn arguments(args: &[String]) -> Result<(Optimization, [&str; 2]), String> {
    let mut optimization = None;
    let mut paths = Vec::new();
    let mut iter = args.iter();
    while let Some(argument) = iter.next() {
        if argument == "--optimization" {
            if optimization.is_some() {
                return Err("duplicate --optimization".into());
            }
            optimization = Some(Optimization::parse(
                iter.next().ok_or("missing --optimization value")?,
            )?);
        } else if argument.starts_with('-') {
            return Err(format!("unknown option {argument}"));
        } else {
            paths.push(argument.as_str());
        }
    }
    let [hull, ir] = paths.as_slice() else {
        return Err(
            "usage: solcore-code-image-export [--optimization O0|O2] HULL.json SONATINA.ir".into(),
        );
    };
    Ok((optimization.unwrap_or(Optimization::O0), [hull, ir]))
}

fn run() -> Result<(), String> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let (optimization, paths) = arguments(&args)?;
    let hull = hull_json(&fs::read_to_string(paths[0]).map_err(|error| error.to_string())?)?;
    if string(&hull, "schema")? != "solcore-rs.hull.v1"
        || string(&hull, "upstreamCommit")? != UPSTREAM
    {
        return Err("unsupported checked Hull schema or revision".into());
    }
    let ir = fs::read_to_string(paths[1]).map_err(|error| error.to_string())?;
    let parsed = sonatina_parser::parse_module(&ir)
        .map_err(|errors| format!("Sonatina IR parse: {errors:?}"))?;
    let artifacts = EvmCompile::new(parsed.module)
        .with_opt_level(optimization.level())
        .with_symbol_table(true)
        .compile()
        .map_err(|errors| format!("Sonatina code generation: {errors:?}"))?;
    let objects = hull
        .get("program")
        .and_then(|program| program.get("objects"))
        .and_then(Value::as_array)
        .ok_or("missing Hull objects")?;
    if objects.is_empty() {
        return Err("code image export requires Hull objects".into());
    }
    if artifacts.len() != objects.len() {
        return Err("backend object count differs from Hull".into());
    }
    let mut images = Vec::new();
    for (index, object) in objects.iter().enumerate() {
        let name = string(object, "name")?;
        let matches = artifacts
            .iter()
            .filter(|artifact| artifact.object.0.as_str() == name)
            .collect::<Vec<_>>();
        let [artifact] = matches.as_slice() else {
            return Err(format!("missing or duplicate compiled object {name}"));
        };
        image(
            object,
            &format!("object{index}"),
            &[],
            "init",
            artifact,
            &mut images,
        )?;
    }
    println!(
        "{}",
        json!({"schema":"solcore-rs.code-images.v1", "upstreamCommit":UPSTREAM,
        "backend":{"name":"sonatina", "revision":BACKEND, "optimization":optimization.name()}, "images":images})
    );
    Ok(())
}

fn main() {
    let result = std::thread::Builder::new()
        .name("code-image-export".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(run)
        .expect("start compiler thread")
        .join()
        .expect("compiler thread panicked");
    if let Err(error) = result {
        eprintln!("code-image-export: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::{arguments, hull_json, Optimization};
    use sonatina_codegen::OptLevel;

    #[test]
    fn optimization_defaults_and_explicit_levels_are_exact() {
        let args = ["hull.json".to_owned(), "program.ir".to_owned()];
        assert_eq!(
            arguments(&args).unwrap(),
            (Optimization::O0, ["hull.json", "program.ir"])
        );
        for (name, expected) in [("O0", Optimization::O0), ("O2", Optimization::O2)] {
            for raw in [
                vec!["--optimization", name, "hull.json", "program.ir"],
                vec!["hull.json", "program.ir", "--optimization", name],
            ] {
                let args = raw.into_iter().map(str::to_owned).collect::<Vec<_>>();
                let (selected, paths) = arguments(&args).unwrap();
                assert_eq!(selected, expected);
                assert_eq!(selected.name(), name);
                assert_eq!(paths, ["hull.json", "program.ir"]);
            }
        }
        assert!(matches!(Optimization::O0.level(), OptLevel::O0));
        assert!(matches!(Optimization::O2.level(), OptLevel::O2));
    }

    #[test]
    fn rejects_ambiguous_or_unsupported_optimization_arguments() {
        for raw in [
            vec!["--optimization"],
            vec!["--optimization", "O1", "h", "i"],
            vec!["--optimization", "o2", "h", "i"],
            vec!["--optimization", "O3", "h", "i"],
            vec!["--optimization", "O0", "--optimization", "O2", "h", "i"],
            vec!["--unknown", "h", "i"],
            vec!["h"],
            vec!["h", "i", "extra"],
        ] {
            let args = raw.into_iter().map(str::to_owned).collect::<Vec<_>>();
            assert!(arguments(&args).is_err(), "{args:?}");
        }
    }

    #[test]
    fn accepts_realistic_deep_hull_and_ignores_string_delimiters() {
        let source = format!("{}0{}", "[".repeat(192), "]".repeat(192));
        assert!(hull_json(&source).is_ok());
        let source = serde_json::to_string(&"[\"\\".repeat(5000)).unwrap();
        assert!(hull_json(&source).is_ok());
    }
    #[test]
    fn rejects_excessive_depth_and_trailing_input() {
        assert!(
            hull_json(&format!("{}0{}", "[".repeat(4097), "]".repeat(4097)))
                .unwrap_err()
                .contains("depth limit")
        );
        for source in ["{}{}", "{} trailing", "", "[}"] {
            assert!(hull_json(source).is_err(), "{source}");
        }
    }
}
