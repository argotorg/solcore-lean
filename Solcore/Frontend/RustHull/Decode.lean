import Solcore.Frontend.RustHull.Syntax
import Solcore.Util.Json

/-! Strict, bounded decoding of the pinned Hull transport. No annotations are inferred here. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull
open Lean

structure DecodeLimits where
  /-- This counts JSON containers and leaves, rather than Hull statements.
  The pinned `basic.sol` transport reaches 283 through generated match arms. -/
  maxDepth : Nat := 512
  maxNodes : Nat := 1000000
  maxStringBytes : Nat := 16777216
  maxInputBytes : Nat := 33554432
  deriving Repr

structure DecodeError where
  path : String
  message : String
  deriving Repr, BEq

abbrev DecodeResult := Except DecodeError

private def fail {α : Type} (path message : String) : DecodeResult α :=
  .error { path, message }

private def field (path : String) (json : Json) (name : String) : DecodeResult Json :=
  (json.getObjVal? name).mapError fun _ => {path := path ++ "." ++ name, message := "missing field"}

private def string (path : String) : Json → DecodeResult String
  | .str value => .ok value
  | _ => fail path "expected string"

private def boolean (path : String) : Json → DecodeResult Bool
  | .bool value => .ok value
  | _ => fail path "expected boolean"

private def natural (path : String) (json : Json) : DecodeResult Nat :=
  match Solcore.Util.jsonNatural? json with
  | some value =>
      if value < 2 ^ 64 then .ok value else fail path "natural number exceeds the upstream 64-bit range"
  | none => fail path "expected natural number"

private def stringField (path : String) (json : Json) (name : String) : DecodeResult String := do
  string (path ++ "." ++ name) (← field path json name)

private def exact (path : String) (json : Json) (required : List String)
    (optional : List String := ["span"]) : DecodeResult Unit := do
  let .obj object := json | fail path "expected object"
  for (key, _) in object.toList do
    unless (required ++ optional).contains key do fail (path ++ "." ++ key) "unknown field"
  for key in required do let _ ← field path json key

private def spanAt (path : String) (json : Json) : DecodeResult Span := do
  exact path json ["file", "start", "end"] []
  let file ← stringField path json "file"
  let start ← natural (path ++ ".start") (← field path json "start")
  let stop ← natural (path ++ ".end") (← field path json "end")
  unless start ≤ stop do fail path "reversed source span"
  pure {file, start, stop}

private def optionalSpan (path : String) (json : Json) : DecodeResult (Option Span) :=
  match json.getObjVal? "span" with
  | .error _ => .ok none
  | .ok value => some <$> spanAt (path ++ ".span") value

private def arrayAt {α : Type} (decode : String → Json → DecodeResult α)
    (path : String) (json : Json) : DecodeResult (List α) := do
  let .arr values := json | fail path "expected array"
  values.toList.zipIdx.mapM fun (value, index) => decode s!"{path}[{index}]" value

private def arrayField {α : Type} (decode : String → Json → DecodeResult α)
    (path : String) (json : Json) (name : String) : DecodeResult (List α) := do
  arrayAt decode (path ++ "." ++ name) (← field path json name)

private def nullable {α : Type} (decode : String → Json → DecodeResult α)
    (path : String) (json : Json) : DecodeResult (Option α) :=
  if json.isNull then .ok none else some <$> decode path json

private structure Budget where
  nodes : Nat := 0
  stringBytes : Nat := 0

private def account (limits : DecodeLimits) (path : String) (bytes : Nat) :
    StateT Budget DecodeResult Unit := do
  let budget ← get
  let next := {nodes := budget.nodes + 1, stringBytes := budget.stringBytes + bytes : Budget}
  if next.nodes > limits.maxNodes then throw {path, message := "JSON node budget exceeded"}
  if next.stringBytes > limits.maxStringBytes then throw {path, message := "JSON string byte budget exceeded"}
  set next

/-- Visit every JSON field, including provenance, before constructing the typed tree. -/
private def preflight (limits : DecodeLimits) : Nat → String → Json → StateT Budget DecodeResult Unit
  | 0, path, _ => throw {path, message := "JSON depth budget exceeded"}
  | fuel + 1, path, json => do
    match json with
    | .str value => account limits path value.utf8ByteSize
    | .arr values =>
      account limits path 0
      for (value, index) in values.toList.zipIdx do preflight limits fuel s!"{path}[{index}]" value
    | .obj object =>
      account limits path 0
      for (key, value) in object.toList do
        account limits (path ++ "." ++ key) key.utf8ByteSize
        preflight limits fuel (path ++ "." ++ key) value
    | _ => account limits path 0

private def decodeTy : Nat → String → Json → DecodeResult Ty
  | 0, path, _ => fail path "type depth budget exceeded"
  | fuel + 1, path, json => do
    let tag ← stringField path json "tag"
    let child := fun key => do decodeTy fuel (path ++ "." ++ key) (← field path json key)
    let value ← match tag with
      | "word" => do exact path json ["tag"]; pure .word
      | "bool" => do exact path json ["tag"]; pure .bool
      | "unit" => do exact path json ["tag"]; pure .unit
      | "product" | "sum" => do
        exact path json ["tag", "left", "right"]
        let left ← child "left"
        let right ← child "right"
        pure (if tag == "product" then .product left right else .sum left right)
      | "named" => do
        exact path json ["tag", "name", "inner"]
        pure (.named (← stringField path json "name") (← child "inner"))
      | "namedRef" => do
        exact path json ["tag", "name"]
        pure (.namedRef (← stringField path json "name"))
      | "function" => do
        exact path json ["tag", "params", "ret"]
        pure (.function (← arrayField (decodeTy fuel) path json "params") (← child "ret"))
      | _ => fail (path ++ ".tag") ("unknown type tag: " ++ tag)
    match ← optionalSpan path json with
    | none => pure value
    | some span => pure (.located span value)

private def decodeExpr : Nat → String → Json → DecodeResult Expr
  | 0, path, _ => fail path "expression depth budget exceeded"
  | fuel + 1, path, json => do
    let tag ← stringField path json "tag"
    let child := fun key => do decodeExpr fuel (path ++ "." ++ key) (← field path json key)
    let target := do decodeTy fuel (path ++ ".target") (← field path json "target")
    let check := fun keys => exact path json (["tag", "ty"] ++ keys)
    let kind ← match tag with
      | "word" => do check ["value"]; pure (.word (← stringField path json "value"))
      | "bool" => do check ["value"]; pure (.bool (← boolean (path ++ ".value") (← field path json "value")))
      | "unit" => do check []; pure .unit
      | "var" => do check ["name"]; pure (.var (← stringField path json "name"))
      | "pair" => do check ["left", "right"]; pure (.pair (← child "left") (← child "right"))
      | "fst" => do check ["value"]; pure (.fst (← child "value"))
      | "snd" => do check ["value"]; pure (.snd (← child "value"))
      | "inl" => do check ["target", "value"]; pure (.inl (← target) (← child "value"))
      | "inr" => do check ["target", "value"]; pure (.inr (← target) (← child "value"))
      | "inK" => do
        check ["index", "target", "value"]
        pure (.inK (← natural (path ++ ".index") (← field path json "index")) (← target) (← child "value"))
      | "call" => do
        check ["callee", "args"]
        pure (.call (← stringField path json "callee") (← arrayField (decodeExpr fuel) path json "args"))
      | "if" => do
        check ["target", "cond", "thenExpr", "elseExpr"]
        pure (.ifThen (← target) (← child "cond") (← child "thenExpr") (← child "elseExpr"))
      | _ => fail (path ++ ".tag") ("unknown expression tag: " ++ tag)
    let ty ← decodeTy fuel (path ++ ".ty") (← field path json "ty")
    pure {ty, kind, span := ← optionalSpan path json}

private def decodeYulLit (path : String) (json : Json) : DecodeResult YulLit := do
  exact path json ["tag", "value"] []
  match ← stringField path json "tag" with
  | "number" => pure (.number (← stringField path json "value"))
  | "hex" => pure (.hex (← stringField path json "value"))
  | "string" => pure (.string (← stringField path json "value"))
  | "bool" => pure (.bool (← boolean (path ++ ".value") (← field path json "value")))
  | tag => fail (path ++ ".tag") ("unknown Yul literal tag: " ++ tag)

private def decodeYulName (path : String) (json : Json) : DecodeResult YulName := do
  exact path json ["name"]
  pure {name := ← stringField path json "name", span := ← optionalSpan path json}

private def decodeYulExpr : Nat → String → Json → DecodeResult YulExpr
  | 0, path, _ => fail path "Yul expression depth budget exceeded"
  | fuel + 1, path, json => do
    let kind ← match ← stringField path json "tag" with
      | "literal" => do
        exact path json ["tag", "value"]
        pure (.literal (← decodeYulLit (path ++ ".value") (← field path json "value")))
      | "ident" => do
        exact path json ["tag", "name"]
        pure (.ident (← decodeYulName (path ++ ".name") (← field path json "name")))
      | "call" => do
        exact path json ["tag", "name", "args"]
        pure (.call (← decodeYulName (path ++ ".name") (← field path json "name"))
          (← arrayField (decodeYulExpr fuel) path json "args"))
      | tag => fail (path ++ ".tag") ("unknown Yul expression tag: " ++ tag)
    pure {kind, span := ← optionalSpan path json}

private def decodeYulStmt : Nat → String → Json → DecodeResult YulStmt
  | 0, path, _ => fail path "Yul statement depth budget exceeded"
  | fuel + 1, path, json => do
    let body := fun key => arrayField (decodeYulStmt fuel) path json key
    let expr := fun key => do decodeYulExpr fuel (path ++ "." ++ key) (← field path json key)
    let names := fun key => arrayField decodeYulName path json key
    let kind ← match ← stringField path json "tag" with
      | "block" => do exact path json ["tag", "body"]; pure (.block (← body "body"))
      | "let" => do
        exact path json ["tag", "names", "init"]
        let names ← names "names"
        if names.isEmpty then fail (path ++ ".names") "expected at least one binding"
        pure (.letDecl names (← nullable (decodeYulExpr fuel) (path ++ ".init") (← field path json "init")))
      | "assign" => do
        exact path json ["tag", "names", "value"]
        let names ← names "names"
        if names.isEmpty then fail (path ++ ".names") "expected at least one target"
        pure (.assign names (← expr "value"))
      | "expr" => do exact path json ["tag", "value"]; pure (.expression (← expr "value"))
      | "if" => do exact path json ["tag", "cond", "body"]; pure (.ifThen (← expr "cond") (← body "body"))
      | "for" => do
        exact path json ["tag", "init", "cond", "post", "body"]
        pure (.forLoop (← body "init") (← expr "cond") (← body "post") (← body "body"))
      | "switch" => do
        exact path json ["tag", "value", "cases", "defaultBody"]
        let cases ← arrayField (fun casePath caseJson => do
          exact casePath caseJson ["lit", "body"]
          let lit ← decodeYulLit (casePath ++ ".lit") (← field casePath caseJson "lit")
          let body ← arrayField (decodeYulStmt fuel) casePath caseJson "body"
          pure ({lit, body, span := ← optionalSpan casePath caseJson} : YulCase)) path json "cases"
        let defaultBody ← nullable (arrayAt (decodeYulStmt fuel)) (path ++ ".defaultBody")
          (← field path json "defaultBody")
        pure (.switch (← expr "value") cases defaultBody)
      | "function" => do
        exact path json ["tag", "name", "params", "rets", "body"]
        pure (.functionDef (← decodeYulName (path ++ ".name") (← field path json "name"))
          (← names "params") (← names "rets") (← body "body"))
      | "leave" => do exact path json ["tag"]; pure .leave
      | "break" => do exact path json ["tag"]; pure .breakStmt
      | "continue" => do exact path json ["tag"]; pure .continueStmt
      | tag => fail (path ++ ".tag") ("unknown Yul statement tag: " ++ tag)
    pure {kind, span := ← optionalSpan path json}

private def decodeCon (path : String) (json : Json) : DecodeResult Con := do
  match ← stringField path json "tag" with
  | "inl" => do exact path json ["tag"] []; pure .inl
  | "inr" => do exact path json ["tag"] []; pure .inr
  | "inK" => do exact path json ["tag", "index"] []; pure (.inK (← natural (path ++ ".index") (← field path json "index")))
  | tag => fail (path ++ ".tag") ("unknown constructor tag: " ++ tag)

private def decodePat (path : String) (json : Json) : DecodeResult Pat := do
  let kind ← match ← stringField path json "tag" with
    | "var" => do exact path json ["tag", "name"]; pure (.var (← stringField path json "name"))
    | "con" => do exact path json ["tag", "value"]; pure (.con (← decodeCon (path ++ ".value") (← field path json "value")))
    | "wildcard" => do exact path json ["tag"]; pure .wildcard
    | "intLit" => do exact path json ["tag", "value"]; pure (.intLit (← stringField path json "value"))
    | tag => fail (path ++ ".tag") ("unknown pattern tag: " ++ tag)
  pure {kind, span := ← optionalSpan path json}

private def decodeStmt : Nat → String → Json → DecodeResult Stmt
  | 0, path, _ => fail path "statement depth budget exceeded"
  | fuel + 1, path, json => do
    let body := fun key => arrayField (decodeStmt fuel) path json key
    let expr := fun key => do decodeExpr fuel (path ++ "." ++ key) (← field path json key)
    let ty := fun key => do decodeTy fuel (path ++ "." ++ key) (← field path json key)
    let kind ← match ← stringField path json "tag" with
      | "let" => do exact path json ["tag", "name", "ty"]; pure (.letDecl (← stringField path json "name") (← ty "ty"))
      | "assign" => do exact path json ["tag", "lhs", "rhs"]; pure (.assign (← expr "lhs") (← expr "rhs"))
      | "expr" => do exact path json ["tag", "value"]; pure (.expression (← expr "value"))
      | "return" => do exact path json ["tag", "value"]; pure (.returnStmt (← expr "value"))
      | "block" => do exact path json ["tag", "body"]; pure (.block (← body "body"))
      | "for" => do
        exact path json ["tag", "init", "cond", "post", "body"]
        pure (.forLoop (← body "init") (← expr "cond") (← body "post") (← body "body"))
      | "break" => do exact path json ["tag"]; pure .breakStmt
      | "continue" => do exact path json ["tag"]; pure .continueStmt
      | "match" => do
        exact path json ["tag", "target", "scrutinee", "alts"]
        let alts ← arrayField (fun altPath altJson => do
          exact altPath altJson ["pat", "binder", "body"]
          let pat ← decodePat (altPath ++ ".pat") (← field altPath altJson "pat")
          let binder ← stringField altPath altJson "binder"
          let body ← arrayField (decodeStmt fuel) altPath altJson "body"
          pure ({pat, binder, body, span := ← optionalSpan altPath altJson} : Alt)) path json "alts"
        pure (.matchStmt (← ty "target") (← expr "scrutinee") alts)
      | "assembly" => do exact path json ["tag", "body"]; pure (.assembly (← arrayField (decodeYulStmt fuel) path json "body"))
      | "revert" => do exact path json ["tag", "message"]; pure (.revert (← stringField path json "message"))
      | "comment" => do exact path json ["tag", "text"]; pure (.comment (← stringField path json "text"))
      | tag => fail (path ++ ".tag") ("unknown statement tag: " ++ tag)
    pure {kind, span := ← optionalSpan path json}

private def decodeArg (fuel : Nat) (path : String) (json : Json) : DecodeResult Arg := do
  exact path json ["name", "ty"]
  let name ← stringField path json "name"
  let ty ← decodeTy fuel (path ++ ".ty") (← field path json "ty")
  pure {name, ty, span := ← optionalSpan path json}

private def decodeFunction (fuel : Nat) (path : String) (json : Json) : DecodeResult Function := do
  exact path json ["name", "args", "ret", "body"]
  let name ← stringField path json "name"
  let args ← arrayField (decodeArg fuel) path json "args"
  let ret ← decodeTy fuel (path ++ ".ret") (← field path json "ret")
  let body ← arrayField (decodeStmt fuel) path json "body"
  pure {name, args, ret, body, span := ← optionalSpan path json}

private def decodeCode (fuel : Nat) (path : String) (json : Json) : DecodeResult CodeBlock := do
  exact path json ["stmts", "functions"]
  let stmts ← arrayField (decodeStmt fuel) path json "stmts"
  let functions ← arrayField (decodeFunction fuel) path json "functions"
  pure {stmts, functions, span := ← optionalSpan path json}

private def decodeObject : Nat → String → Json → DecodeResult Object
  | 0, path, _ => fail path "object depth budget exceeded"
  | fuel + 1, path, json => do
    exact path json ["name", "code", "inners"]
    pure (.object (← stringField path json "name")
      (← decodeCode fuel (path ++ ".code") (← field path json "code"))
      (← arrayField (decodeObject fuel) path json "inners") (← optionalSpan path json))

/-- Decode all supplied functions and objects, rejecting unknown fields and schema revisions. -/
def decode (json : Json) (limits : DecodeLimits := {}) : DecodeResult Envelope := do
  let _ ← (preflight limits limits.maxDepth "$" json).run {}
  exact "$" json ["schema", "upstreamCommit", "program"] []
  unless (← stringField "$" json "schema") == schemaName do fail "$.schema" "unsupported Hull schema"
  unless (← stringField "$" json "upstreamCommit") == upstreamCommit do
    fail "$.upstreamCommit" "unsupported upstream revision"
  let program ← field "$" json "program"
  exact "$.program" program ["entryPoints", "functions", "objects"]
  pure {program := {
    entryPoints := ← arrayField string "$.program" program "entryPoints",
    functions := ← arrayField (decodeFunction limits.maxDepth) "$.program" program "functions",
    objects := ← arrayField (decodeObject limits.maxDepth) "$.program" program "objects",
    span := ← optionalSpan "$.program" program}}

private structure TextScan where
  depth : Nat := 0
  quoted : Bool := false
  escaped : Bool := false
  digits : Nat := 0
  valid : Bool := true

/-- Check nesting and canonical numeric tokens before JSON parsing can allocate
an enormous exponent or recurse through an adversarially deep document. -/
private def scanText (maxDepth : Nat) (state : TextScan) (char : Char) : TextScan :=
  if !state.valid then state
  else if state.quoted then
    if state.escaped then {state with escaped := false}
    else if char == '\\' then {state with escaped := true}
    else if char == '"' then {state with quoted := false}
    else state
  else if char.isDigit then
    {state with digits := state.digits + 1, valid := state.digits < 20}
  else if state.digits > 0 && !(char.isWhitespace || char == ',' || char == ']' || char == '}') then
    {state with valid := false}
  else
    let state := {state with digits := 0}
    if char == '"' then {state with quoted := true}
    else if char == '[' || char == '{' then
      {state with depth := state.depth + 1, valid := state.depth < maxDepth}
    else if char == ']' || char == '}' then {state with depth := state.depth - 1}
    else if char == '-' then {state with valid := false}
    else state

/-- Bound textual input before invoking Lean's JSON parser. Numeric fields in
this transport use unsigned decimal integers, as emitted by the Rust exporter. -/
def decodeText (text : String) (limits : DecodeLimits := {}) : DecodeResult Envelope := do
  if text.utf8ByteSize > limits.maxInputBytes then fail "$" "JSON input byte budget exceeded"
  unless (text.foldl (scanText limits.maxDepth) {}).valid do
    fail "$" "JSON nesting or numeric token limit exceeded"
  let json ← Json.parse text |>.mapError fun message => {path := "$", message}
  decode json limits

end Solcore.Frontend.RustHull
