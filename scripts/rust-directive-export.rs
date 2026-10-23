//! Export the pinned parser's attached comments and test-directives AST.
use hir::{
    ast::item::{ContractItem, FuncKind, Item},
    input::SourceFile,
};
use serde_json::{Value, json};
use solcore_test_directives::{
    DirectiveValue, E2eAction, E2eDirective, ExpectedOutcome, RawE2eVector,
    ResolvedExpectedOutcome, parse_e2e_directive,
};
use std::{env, fs, path::Path};

const COMMIT: &str = "2a745e12974c373c3799fec81b48a53c7dce2ab4";

#[salsa::db]
#[derive(Default, Clone)]
struct Db {
    storage: salsa::Storage<Self>,
}
#[salsa::db]
impl salsa::Database for Db {}
#[salsa::db]
impl hir::Db for Db {
    fn def_location_table<'db>(
        &'db self,
        file: SourceFile,
    ) -> &'db hir::anchor::DefLocationTable<'db> {
        parser::parse_file_to_hir(self, file).def_locations(self)
    }
}
#[salsa::db]
impl parser::Db for Db {}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::from("0x");
    for byte in bytes {
        use std::fmt::Write;
        write!(result, "{byte:02x}").unwrap();
    }
    result
}

fn value(value: &DirectiveValue) -> Value {
    match value {
        DirectiveValue::Word(word) => json!({"kind":"word", "value":word.to_string()}),
        DirectiveValue::Bool(value) => json!({"kind":"bool", "value":value}),
        DirectiveValue::Tuple(values) => {
            json!({"kind":"tuple", "values":values.iter().map(self::value).collect::<Vec<_>>()})
        }
    }
}

fn parsed(directive: &E2eDirective) -> Value {
    let action = match &directive.action {
        E2eAction::Send => json!({"kind":"send"}),
        E2eAction::Call(ExpectedOutcome::Return(values)) => {
            json!({"kind":"call", "expected":{"status":"returned", "values":values.iter().map(value).collect::<Vec<_>>()}})
        }
        E2eAction::Call(ExpectedOutcome::Revert(output)) => {
            json!({"kind":"call", "expected":{"status":"reverted", "output":output.as_ref().map(|bytes| hex(bytes))}})
        }
    };
    json!({"arguments":directive.args.iter().map(value).collect::<Vec<_>>(), "action":action})
}

fn expected(expected: &ResolvedExpectedOutcome) -> Value {
    match expected {
        ResolvedExpectedOutcome::Return(output) => {
            json!({"status":"returned", "output":hex(output)})
        }
        ResolvedExpectedOutcome::Revert(output) => {
            json!({"status":"reverted", "output":output.as_ref().map(|bytes| hex(bytes))})
        }
    }
}

fn scenario(vector: &RawE2eVector) -> Value {
    json!({"name":vector.name, "contract":vector.contract, "evmVersionMetadata":vector.evm_version,
        "effectiveEvmVersion":vector.effective_evm_version(),
        "constructor":{"calldata":hex(&vector.constructor.calldata), "value":vector.constructor.value.to_string(),
            "expectedSuccess":vector.constructor.expected_success,
            "expectedOutput":vector.constructor.expected_output.as_ref().map(|bytes| hex(bytes))},
        "calls":vector.calls.iter().map(|call| json!({"label":call.label, "calldata":call.calldata,
            "value":call.value.to_string(), "expected":expected(&call.expected)})).collect::<Vec<_>>()})
}

fn extract(path: &Path) -> Result<Value, String> {
    let source = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let db = Db::default();
    let file = SourceFile::new(
        &db,
        url::Url::from_file_path(path).map_err(|_| "invalid source path")?,
        Some(source),
    );
    let hir = parser::parse_file_to_hir(&db, file);
    if !hir.diagnostics(&db).is_empty() {
        return Err(format!(
            "source parser returned {} diagnostics",
            hir.diagnostics(&db).len()
        ));
    }
    let module = hir.module(&db);
    // Use exactly the upstream HIR selection rules: comment ownership, mixed
    // mode checks, misplaced directives, and one raw scenario per fixture.
    let raw = solcore_test_utils::e2e::source_e2e_scenario(&db, module)
        .map_err(|error| format!("{:?}: {}", error.kind, error.message))?;
    let mut contracts = Vec::new();
    let mut targets = Vec::new();
    for item in module.items(&db) {
        let misplaced = match item {
            Item::FunctionDef(function) => vec![*function],
            Item::InstanceDef(instance) => instance.methods(&db).to_vec(),
            _ => Vec::new(),
        };
        for function in misplaced {
            for comment in function.leading_comments(&db) {
                if parse_e2e_directive(&comment.text)
                    .map_err(|error| error.to_string())?
                    .is_some()
                {
                    return Err("method directives must target a public contract function".into());
                }
            }
        }
        let Item::ContractDef(contract) = item else {
            continue;
        };
        let name = contract.name_elem(&db).atom().text(&db).to_owned();
        contracts.push(name.clone());
        for item in contract.items(&db) {
            let ContractItem::FunctionDef(function) = item else {
                continue;
            };
            let mut directives = Vec::new();
            for comment in function.leading_comments(&db) {
                if let Some(directive) =
                    parse_e2e_directive(&comment.text).map_err(|error| error.to_string())?
                {
                    directives
                        .push(json!({"comment":comment.text, "directive":parsed(&directive)}));
                }
            }
            if directives.is_empty() {
                continue;
            }
            let method = function.sig(&db).name.atom().text(&db);
            if function.kind(&db) != FuncKind::Function
                || function.sig(&db).public.is_none()
                || method == "main"
                || contract.has_runtime_main(&db)
            {
                return Err(format!(
                    "{name}::{method}: directive target is not a selector-dispatched public method"
                ));
            }
            targets.push(json!({"contract":name, "method":method, "directives":directives}));
        }
    }
    let mode = if raw.is_some() {
        "raw"
    } else if !targets.is_empty() {
        "methods"
    } else {
        "none"
    };
    Ok(
        json!({"schema":"solcore-rs.test-directives.v1", "upstreamCommit":COMMIT,
        "source":path.to_string_lossy(), "mode":mode, "contracts":contracts,
        "scenario":raw.as_ref().map(scenario), "methods":targets}),
    )
}

fn main() {
    let result = (|| {
        let path = env::args()
            .nth(1)
            .ok_or("usage: solcore-directive-export SOURCE.sol")?;
        extract(
            &Path::new(&path)
                .canonicalize()
                .map_err(|error| error.to_string())?,
        )
    })();
    match result {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
