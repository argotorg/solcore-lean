//! Resolve attached method directives with the pinned upstream ABI encoder.
use serde_json::{Value, json};
use solcore_test_directives::{
    AbiShape, ResolvedE2eAction, ResolvedExpectedOutcome, parse_e2e_directive,
    resolve_e2e_directive,
};
use std::{env, fs};

const COMMIT: &str = "2a745e12974c373c3799fec81b48a53c7dce2ab4";

fn text<'a>(value: &'a Value, key: &str) -> Result<&'a str, String> {
    value[key]
        .as_str()
        .ok_or_else(|| format!("missing string {key}"))
}
fn array<'a>(value: &'a Value, key: &str) -> Result<&'a Vec<Value>, String> {
    value[key]
        .as_array()
        .ok_or_else(|| format!("missing array {key}"))
}
fn shape(value: &Value) -> Result<AbiShape, String> {
    Ok(match text(value, "type")? {
        "uint256" => AbiShape::Word,
        "bool" => AbiShape::Bool,
        "address" => AbiShape::Address,
        "bytes32" => AbiShape::Bytes32,
        "tuple" => {
            let children = array(value, "components")?
                .iter()
                .map(shape)
                .collect::<Result<Vec<_>, _>>()?;
            if children.is_empty() {
                AbiShape::Unit
            } else {
                AbiShape::Tuple(children)
            }
        }
        other => AbiShape::Unsupported(other.to_owned()),
    })
}
fn hex(bytes: &[u8]) -> String {
    let mut result = String::from("0x");
    for byte in bytes {
        use std::fmt::Write;
        write!(result, "{byte:02x}").unwrap();
    }
    result
}
fn resolve(document: Value) -> Result<Value, String> {
    if text(&document, "schema")? != "solcore-rs.method-resolution-input.v1" {
        return Err("unsupported resolver input schema".into());
    }
    let mut calls = Vec::new();
    for target in array(&document, "targets")? {
        let selector = text(target, "selector")?;
        if selector.len() != 10
            || !selector.starts_with("0x")
            || !selector[2..].bytes().all(|b| b.is_ascii_hexdigit())
        {
            return Err("selector must contain four hexadecimal bytes".into());
        }
        let mut bytes = [0u8; 4];
        for (index, byte) in bytes.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&selector[2 + index * 2..4 + index * 2], 16)
                .map_err(|error| error.to_string())?;
        }
        let inputs = array(target, "inputs")?
            .iter()
            .map(shape)
            .collect::<Result<Vec<_>, _>>()?;
        let outputs = array(target, "outputs")?
            .iter()
            .map(shape)
            .collect::<Result<Vec<_>, _>>()?;
        for (index, comment) in array(target, "comments")?.iter().enumerate() {
            let comment = comment
                .as_str()
                .ok_or("directive comment must be a string")?;
            let directive = parse_e2e_directive(comment)
                .map_err(|error| error.to_string())?
                .ok_or("expected a directive comment")?;
            let call = resolve_e2e_directive(
                text(target, "signature")?,
                bytes,
                &inputs,
                &outputs,
                &directive,
            )
            .map_err(|error| error.to_string())?;
            let (persist, expected) = match call.action {
                ResolvedE2eAction::Send => (true, json!({"status":"returned", "output":null})),
                ResolvedE2eAction::Call(ResolvedExpectedOutcome::Return(output)) => {
                    (false, json!({"status":"returned", "output":hex(&output)}))
                }
                ResolvedE2eAction::Call(ResolvedExpectedOutcome::Revert(output)) => (
                    false,
                    json!({"status":"reverted", "output":output.as_ref().map(|bytes| hex(bytes))}),
                ),
            };
            calls.push(json!({"contract":text(target,"contract")?, "method":text(target,"method")?,
                "vector":index + 1, "signature":call.signature, "selector":selector,
                "calldata":call.calldata, "persist":persist, "expected":expected, "comment":comment}));
        }
    }
    Ok(json!({"schema":"solcore-rs.resolved-methods.v1", "upstreamCommit":COMMIT, "calls":calls}))
}
fn main() {
    let result = (|| {
        let path = env::args()
            .nth(1)
            .ok_or("usage: solcore-directive-resolve INPUT.json")?;
        let document =
            serde_json::from_str(&fs::read_to_string(path).map_err(|error| error.to_string())?)
                .map_err(|error| error.to_string())?;
        resolve(document)
    })();
    match result {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
