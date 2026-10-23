import Solcore.Frontend.RustHull.Decode

/-! Import-boundary regressions for complete Hull transport and strict rejection. -/
set_option autoImplicit false
namespace Tests.RustHullDecode
open Lean Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def sample : String := r#"{
  "schema":"solcore-rs.hull.v1",
  "upstreamCommit":"2a745e12974c373c3799fec81b48a53c7dce2ab4",
  "program":{
    "entryPoints":["entry"],
    "span":{"file":"main.sol","start":0,"end":120},
    "functions":[{
      "name":"entry",
      "args":[{"name":"x","ty":{"tag":"named","name":"N","inner":{"tag":"sum","left":{"tag":"unit"},"right":{"tag":"word"}}}}],
      "ret":{"tag":"word","span":{"file":"main.sol","start":30,"end":34}},
      "body":[{
        "tag":"match","target":{"tag":"word"},
        "scrutinee":{"tag":"var","ty":{"tag":"namedRef","name":"N"},"name":"x"},
        "alts":[{
          "pat":{"tag":"con","value":{"tag":"inK","index":1}},"binder":"payload",
          "body":[{"tag":"return","value":{"tag":"word","ty":{"tag":"word"},"value":"0xffff"}}]
        }]
      }]
    }],
    "objects":[{
      "name":"Deployment","code":{"functions":[],"stmts":[{
        "tag":"assembly","body":[{
          "tag":"function","name":{"name":"choose"},"params":[{"name":"a"}],"rets":[{"name":"b"}],
          "body":[{
            "tag":"switch","value":{"tag":"ident","name":{"name":"a"}},
            "cases":[{"lit":{"tag":"number","value":"0"},"body":[{"tag":"assign","names":[{"name":"b"}],"value":{"tag":"literal","value":{"tag":"hex","value":"0xff"}}}]}],
            "defaultBody":null
          },{"tag":"leave"}]
        },{
          "tag":"let","names":[{"name":"result"}],
          "init":{"tag":"call","name":{"name":"choose","span":{"file":"main.sol","start":98,"end":104}},"args":[{"tag":"literal","value":{"tag":"number","value":"0"}}]}
        }]
      }]},
      "inners":[{"name":"Runtime","code":{"stmts":[],"functions":[]},"inners":[]}]
    }]
  }
}"#

private def put (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert key value)
  | _ => json

private def rejects (json : Json) (path : String) (limits : DecodeLimits := {}) : IO Unit :=
  match decode json limits with
  | .ok _ => throw (IO.userError s!"Hull decoder accepted malformed input at {path}")
  | .error error => require (error.path == path)
      s!"Hull decoder error path changed: expected {path}, got {reprStr error}"

/-- Generated pattern matches contain statement objects inside body arrays;
even a moderate Hull nesting depth therefore exceeds 256 JSON levels. -/
private def nestedStatements (count : Nat) (leaf : String := "{\"tag\":\"comment\",\"text\":\"leaf\"}") : String :=
  (List.range count).foldl (fun body _ => "{\"tag\":\"block\",\"body\":[" ++ body ++ "]}") leaf

private def nestedProgram (count : Nat) (leaf : String := "{\"tag\":\"comment\",\"text\":\"leaf\"}") : String :=
  "{\"schema\":\"" ++ schemaName ++ "\",\"upstreamCommit\":\"" ++ upstreamCommit ++
  "\",\"program\":{\"entryPoints\":[],\"objects\":[],\"functions\":[{\"name\":\"deep\",\"args\":[]," ++
  "\"ret\":{\"tag\":\"unit\"},\"body\":[" ++ nestedStatements count leaf ++ "]}]}}"

private def blockDepth : List Stmt → Nat
  | [{kind := .block body, ..}] => blockDepth body + 1
  | _ => 0

private def deepInputs : IO Unit := do
  let deep := nestedProgram 140
  let decoded ← match decodeText deep with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"Hull decoder rejected generated-depth input: {reprStr error}")
  match decoded.program.functions with
  | [function] =>
    require (blockDepth function.body == 140) "Hull decoder truncated generated nested statements"
  | _ => throw (IO.userError "Hull decoder lost the nested function")
  match decodeText deep {maxDepth := 256} with
  | .error error =>
    require (error.message == "JSON nesting or numeric token limit exceeded")
      "Hull decoder stopped enforcing the caller's depth limit"
  | .ok _ => throw (IO.userError "Hull decoder ignored an explicit depth limit")
  -- Root, program, functions, function, body, comment, text have depth seven;
  -- each enclosing block adds an object and array. The leaf reaches 511 here.
  match decodeText (nestedProgram 252) {maxDepth := 511},
      decodeText (nestedProgram 252) {maxDepth := 510} with
  | .ok _, .error error =>
    require (error.message == "JSON depth budget exceeded")
      "Hull decoder did not count the deepest scalar leaf"
  | _, _ => throw (IO.userError "Hull decoder changed its exact depth boundary")
  match decodeText (nestedProgram 254) with
  | .error error =>
    require (error.message == "JSON nesting or numeric token limit exceeded")
      "Hull decoder parsed text beyond its default nesting limit"
  | .ok _ => throw (IO.userError "Hull decoder accepted excessive default nesting")
  match decodeText (nestedProgram 140 "{\"tag\":\"future\"}") with
  | .error error =>
    require (error.message == "unknown statement tag: future")
      "Hull decoder skipped validation of deeply nested statements"
  | .ok _ => throw (IO.userError "Hull decoder accepted an unknown nested statement")

def run : IO Unit := do
  let envelope ← match decodeText sample with
    | .ok value => pure value
    | .error error => throw (IO.userError (reprStr error))
  require (envelope.program.entryPoints == ["entry"]) "Hull decoder lost entry point order"
  require (envelope.program.span == some {file := "main.sol", start := 0, stop := 120})
    "Hull decoder lost resolved source provenance"
  let function ← match envelope.program.functions with
    | [function] => pure function
    | _ => throw (IO.userError "Hull decoder lost function boundaries")
  require (function.ret == .located {file := "main.sol", start := 30, stop := 34} .word)
    "Hull decoder dropped type provenance"
  require (function.args.map (·.ty) == [.named "N" (.sum .unit .word)])
    "Hull decoder changed argument annotations"
  let alt ← match function.body with
    | [{kind := .matchStmt .word scrutinee [alt], ..}] =>
      require (scrutinee.ty == .namedRef "N" && scrutinee.kind == .var "x")
        "Hull decoder changed recursive type references"
      pure alt
    | _ => throw (IO.userError "Hull decoder changed match structure")
  require (alt.pat.kind == .con (.inK 1) && alt.binder == "payload")
    "Hull decoder changed constructor indices or binders"
  match alt.body with
  | [{kind := .returnStmt value, ..}] =>
    require (value.ty == .word && value.kind == .word "0xffff")
      "Hull decoder changed literal text"
  | _ => throw (IO.userError "Hull decoder lost a return")
  let code ← match envelope.program.objects with
    | [.object "Deployment" code [.object "Runtime" inner [] none] none] =>
      require (inner.stmts.isEmpty && inner.functions.isEmpty) "Hull decoder changed inner code"
      pure code
    | _ => throw (IO.userError "Hull decoder changed nested objects")
  let assembly ← match code.stmts with
    | [{kind := .assembly assembly, ..}] => pure assembly
    | _ => throw (IO.userError "Hull decoder lost assembly")
  match assembly with
  | [{kind := .functionDef name params rets body, ..}, {kind := .letDecl names (some init), ..}] =>
    require (name.name == "choose" && params.map (·.name) == ["a"] && rets.map (·.name) == ["b"])
      "Hull decoder changed Yul function signatures"
    match body with
    | [{kind := .switch _ [arm] none, ..}, {kind := .leave, ..}] =>
      require (arm.lit == .number "0" && arm.body.length == 1) "Hull decoder changed switch cases"
    | _ => throw (IO.userError "Hull decoder changed Yul function scopes")
    require (names.map (·.name) == ["result"]) "Hull decoder changed Yul bindings"
    match init.kind with
    | .call name [_] =>
      require (name.name == "choose" && name.span == some {file := "main.sol", start := 98, stop := 104})
        "Hull decoder lost Yul identifier provenance"
    | _ => throw (IO.userError "Hull decoder changed Yul calls")
  | _ => throw (IO.userError "Hull decoder changed assembly boundaries")
  let json ← match Json.parse sample with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  rejects (put json "schema" (.str "other")) "$.schema"
  rejects (put json "upstreamCommit" (.str "unreviewed")) "$.upstreamCommit"
  rejects (put json "ignored" (.bool true)) "$.ignored"
  let program := json.getObjValD "program"
  rejects (put json "program" (put program "objects" (.str "lost"))) "$.program.objects"
  rejects (put json "program" (put program "span" (.mkObj [
    ("file", .str "main.sol"), ("start", toJson (9 : Nat)), ("end", toJson (1 : Nat))]))) "$.program.span"
  let unknown := Json.mkObj [("tag", .str "future"), ("ty", .mkObj [("tag", .str "unit")])]
  let function := Json.mkObj [("name", .str "main"), ("args", .arr #[]),
    ("ret", .mkObj [("tag", .str "unit")]),
    ("body", .arr #[.mkObj [("tag", .str "return"), ("value", unknown)]])]
  rejects (put json "program" (put program "functions" (.arr #[function])))
    "$.program.functions[0].body[0].value.tag"
  rejects json "$" {maxDepth := 0}
  rejects json "$" {maxNodes := 0}
  match decode json {maxStringBytes := 1} with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Hull decoder ignored string byte budget")
  match decodeText sample {maxInputBytes := 1}, decodeText "{", decodeText "[1e999999999]",
      decodeText "[[[[[]]]]]" {maxDepth := 3} with
  | .error _, .error _, .error _, .error _ => pure ()
  | _, _, _, _ => throw (IO.userError "Hull text decoder ignored byte, syntax, numeric, or nesting limits")
  deepInputs

end Tests.RustHullDecode
