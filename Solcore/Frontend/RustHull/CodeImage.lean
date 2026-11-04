import Solcore.Frontend.RustHull.Syntax
import Solcore.Frontend.RustHull.Memory
import Solcore.Util.Json
import Solcore.Frontend.RustHull.LoweringSupport

/-!
# Linked code images

Exact object bytes, their linking and their comparison on Core. Main declarations:
`CodeImage.Image`, `CodeImage.resolve`, `ObjectLinking.link`, `ImageComparison`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.CodeImage
/-! Exact linked object bytes for code inspection and constructor execution.
The bytes and symbol offsets come from a pinned backend artifact. Validation
checks their structural correspondence to Hull objects and embedded images;
it does not establish correctness of the backend's instruction selection. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.CodeImage

structure Extent where
  offset : Nat
  size : Nat
  deriving Repr, BEq

structure Embed extends Extent where
  name : String
  deriving Repr, BEq

structure Image where
  path : List String
  bytes : List UInt8
  embeds : List Embed := []
  deriving Repr, BEq

def schema : String := "solcore-rs.code-images.v1"
def backendRevision : String := "6bd0ce661ea327c149429b00fee3c8608616040f"

private def unique {α : Type} [BEq α] (values : List α) : Bool :=
  (values.eraseDups).length == values.length

def select (images : List Image) (path : List String) : Except String Image :=
  match images.filter (·.path == path) with
  | [image] => pure image
  | [] => .error s!"no linked byte image for object {reprStr path}"
  | _ => .error s!"duplicate linked byte image for object {reprStr path}"

private def entries (parent : List String) : List Object → List (List String × List String)
  | [] => []
  | .object name _ children _ :: rest =>
      let path := parent ++ [name]
      (path, children.map fun (.object child _ _ _) => child) ::
        (entries path children ++ entries parent rest)

/-- Require complete, unambiguous image coverage and exact direct-child bytes.
A symbol's offsets are relative to its containing image. Nested symbols stay
in the child image, matching the backend's section-local linker namespace. -/
def validate (objects : List Object) (images : List Image) : Except String Unit := do
  let expected := entries [] objects
  unless unique (expected.map Prod.fst) do throw "ambiguous Hull object paths"
  unless unique (images.map Image.path) do throw "duplicate linked object paths"
  unless images.length = expected.length do throw "linked image inventory differs from Hull objects"
  for image in images do
    unless expected.any (fun item => item.1 == image.path) do
      throw s!"linked image has no Hull object: {reprStr image.path}"
  for (path, children) in expected do
    let image ← select images path
    unless image.bytes.length < Core.wordModulus do throw "linked image exceeds the word address space"
    unless unique children && unique (image.embeds.map Embed.name) do
      throw s!"duplicate embedded object names in {reprStr path}"
    unless children.length = image.embeds.length &&
        children.all (fun name => image.embeds.any (·.name == name)) do
      throw s!"embedded symbols differ from direct Hull children in {reprStr path}"
    for embedded in image.embeds do
      if path.getLast? == some embedded.name then
        throw s!"embedded name shadows its containing object: {embedded.name}"
      unless embedded.offset + embedded.size ≤ image.bytes.length do
        throw s!"embedded symbol lies outside its image: {embedded.name}"
      let child ← select images (path ++ [embedded.name])
      unless embedded.size = child.bytes.length &&
          (image.bytes.drop embedded.offset).take embedded.size == child.bytes do
        throw s!"embedded bytes differ from the child image: {embedded.name}"
    for (embedded, index) in image.embeds.zipIdx do
      for later in image.embeds.drop (index + 1) do
        unless embedded.size = 0 || later.size = 0 ||
            embedded.offset + embedded.size ≤ later.offset ||
            later.offset + later.size ≤ embedded.offset do
          throw s!"overlapping embedded symbols: {embedded.name}, {later.name}"

/-- The current object's extent excludes any appended constructor arguments. -/
def resolve (image : Image) (symbol : String) : Except String Extent :=
  if image.path.getLast? == some symbol then pure ⟨0, image.bytes.length⟩
  else match image.embeds.filter (·.name == symbol) with
    | [embedded] => pure embedded.toExtent
    | [] => .error s!"unknown linked object symbol: {symbol}"
    | _ => .error s!"ambiguous linked object symbol: {symbol}"

/-- Init code sees its constructor input appended to the compiled section.
Runtime code uses an empty suffix. No byte lengths or contents are fabricated. -/
def executionBytes (image : Image) (constructorArguments : List UInt8 := []) : Except String (List UInt8) :=
  if image.bytes.length + constructorArguments.length < Core.wordModulus then
    pure (image.bytes ++ constructorArguments)
  else .error "executing code exceeds the word address space"

def mapping (bytes : List UInt8) : Core.Expr :=
  Core.WordMapping.literal (bytes.zipIdx.map fun (value, offset) =>
    (Core.Word.ofNatModulo offset, Core.Word.ofNatModulo value.toNat))

/-- The caller uses validated execution bytes, including any constructor input. -/
def codeSize (bytes : List UInt8) : Core.Expr :=
  Core.LanguageResult.success (.word (Core.Word.ofNatModulo bytes.length))

/-- Copy actual code bytes with EVM zero padding. Source offsets do not wrap;
only the destination contributes to memory expansion. -/
def copy (bytes : List UInt8) (memoryReference sizeReference destination source length : Core.Expr) : Core.Expr :=
  Memory.copyFrom memoryReference sizeReference destination (mapping bytes) source length

private def field (json : Lean.Json) (name : String) : Except String Lean.Json :=
  (json.getObjVal? name).mapError fun _ => s!"missing code image field: {name}"

private def exact (json : Lean.Json) (names : List String) : Except String Unit := do
  let .obj values := json | throw "code image object expected"
  for (key, _) in values.toList do
    unless names.contains key do throw s!"unexpected code image field: {key}"
  for name in names do let _ ← field json name

private def text (json : Lean.Json) : Except String String :=
  json.getStr?.mapError fun _ => "code image string expected"

private def natural (json : Lean.Json) : Except String Nat :=
  match Solcore.Util.jsonNatural? json with
  | some value => if value < 2 ^ 32 then pure value else .error "code image extent exceeds backend u32 range"
  | none => .error "code image natural number expected"

private def array {α : Type} (decode : Lean.Json → Except String α)
    (json : Lean.Json) : Except String (List α) := do
  let .arr values := json | throw "code image array expected"
  values.toList.mapM decode

private def nibble (char : Char) : Except String Nat :=
  if '0' ≤ char && char ≤ '9' then pure (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then pure (char.toNat - 'a'.toNat + 10)
  else .error "code image bytes must use lowercase hexadecimal"

private def hexBytes (accumulator : List UInt8) : List Char → Except String (List UInt8)
  | [] => pure accumulator.reverse
  | left :: right :: rest => do
      let byte := 16 * (← nibble left) + (← nibble right)
      hexBytes (UInt8.ofNat byte :: accumulator) rest
  | [_] => .error "code image has an incomplete byte"

private def decodeBytes (json : Lean.Json) : Except String (List UInt8) := do
  let value ← text json
  let '0' :: 'x' :: rest := value.toList | throw "code image must start with 0x"
  hexBytes [] rest

private def decodeEmbed (json : Lean.Json) : Except String Embed := do
  exact json ["name", "offset", "size"]
  let name ← text (← field json "name")
  let offset ← natural (← field json "offset")
  let size ← natural (← field json "size")
  return {name, offset, size}

private def decodeImage (json : Lean.Json) : Except String Image := do
  exact json ["path", "bytes", "embeds"]
  let path ← array text (← field json "path")
  unless !path.isEmpty && path.all (fun name => !name.isEmpty) do throw "empty code image object path"
  let bytes ← decodeBytes (← field json "bytes")
  let embeds ← array decodeEmbed (← field json "embeds")
  return {path, bytes, embeds}

private structure TextScan where
  depth : Nat := 0
  quoted : Bool := false
  escaped : Bool := false
  digits : Nat := 0
  valid : Bool := true

private def scanText (state : TextScan) (char : Char) : TextScan :=
  if !state.valid then state
  else if state.quoted then
    if state.escaped then {state with escaped := false}
    else if char == '\\' then {state with escaped := true}
    else if char == '"' then {state with quoted := false}
    else state
  else if char.isDigit then
    {state with digits := state.digits + 1, valid := state.digits < 10}
  else if state.digits > 0 && !(char.isWhitespace || char == ',' || char == ']' || char == '}') then
    {state with valid := false}
  else
    let state := {state with digits := 0}
    if char == '"' then {state with quoted := true}
    else if char == '[' || char == '{' then
      {state with depth := state.depth + 1, valid := state.depth < 16}
    else if char == ']' || char == '}' then {state with depth := state.depth - 1}
    else if char == '-' then {state with valid := false}
    else state

/-- Decode a bounded, revision-pinned backend artifact. Call `validate` with
its corresponding checked Hull objects before preparing execution. -/
def decode (input : String) (maxInputBytes : Nat := 33554432) : Except String (List Image) := do
  if input.utf8ByteSize > maxInputBytes then throw "code image input exceeds its byte limit"
  unless (input.foldl scanText {}).valid do throw "code image nesting or numeric token limit exceeded"
  let json ← Lean.Json.parse input
  exact json ["schema", "upstreamCommit", "backend", "images"]
  unless (← text (← field json "schema")) = schema do throw "unsupported code image schema"
  unless (← text (← field json "upstreamCommit")) = RustHull.upstreamCommit do
    throw "code image upstream revision mismatch"
  let backend ← field json "backend"
  exact backend ["name", "revision", "optimization"]
  let optimization ← text (← field backend "optimization")
  unless (← text (← field backend "name")) = "sonatina" &&
      (← text (← field backend "revision")) = backendRevision &&
      (optimization = "O0" || optimization = "O2") do
    throw "unsupported code image backend configuration"
  array decodeImage (← field json "images")

end Solcore.Frontend.RustHull.CodeImage
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ImageComparison
/-! Exact packed image comparison on Core. One pass over the input mapping
uses a bitmap to preserve first-key semantics, including duplicate and missing
entries. A balanced constant table avoids repeated linear mapping lookups. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ImageComparison
open Core CodeBuilder

private def table (values : List Code) (key : Code) (base : Nat := 0) : Code :=
  match _equality : values with
  | [] => number 0
  | [value] => value
  | _ :: _ :: _ =>
    let middle := values.length / 2
    choose (binary .wordGt (number (base + middle)) key)
      (table (values.take middle) key base)
      (table (values.drop middle) key (base + middle))
termination_by values.length
 decreasing_by all_goals simp_wf; simp_all only [List.length_cons]; omega

private def compareBody (bytes : List UInt8) : Core.Expr := Id.run do
  let count := (bytes.length + 31) / 32
  let buckets := (count + 255) / 256
  let masksType := bundleType (List.replicate buckets .word)
  let parameter := Core.Ty.product WordMapping.type masksType
  let entries := Memory.packBytes bytes
  let words := (List.range count).map fun index =>
    WordMapping.lookupEntries (Word.ofNatModulo index) entries
  let needed := (List.range buckets).map fun bucket =>
    (List.range (min 256 (count - bucket * 256))).foldl (fun mask offset =>
      if (words[bucket * 256 + offset]?.getD Word.zero).val == 0 then mask else mask + 2 ^ offset) 0
  let complete (masks : Code) := needed.zipIdx.foldr (fun (bits, index) next =>
    choose (binary .wordEq (binary .wordAnd (part index buckets masks) (number bits)) (number bits))
      next (success (boolean false))) (success (boolean true))
  let step := bind (constant (bundle [.var 0, .var 1, .var 2])) fun args =>
    let entry := part 0 3 args
    let key := part 0 2 (part 0 2 entry)
    let value := part 1 2 (part 0 2 entry)
    let tail := part 1 2 entry
    let seen := part 1 2 (part 1 3 args)
    let recurse (masks : Code) : Code := fun depth => WordMapping.invoke parameter .bool
      (part 2 3 args depth) (.pair (tail depth) (masks depth))
    choose (binary .wordGt (number count) key)
      (bind (binary .wordDiv key (number 256)) fun bucket =>
       bind (binary .wordShl (number 1) (binary .wordMod key (number 256))) fun bit =>
       bind (table ((List.range buckets).map fun index => part index buckets seen) bucket) fun mask =>
       choose (binary .wordEq (binary .wordAnd mask bit) (number 0))
         (let expected := table (words.map (constant ∘ Core.Expr.word)) key
          let shift := choose (binary .wordEq key (number (count - 1)))
            (number ((32 - (bytes.length - (count - 1) * 32)) * 8)) (number 0)
          choose (binary .wordEq (binary .wordShr value shift) (binary .wordShr expected shift))
            (recurse (packet ((List.range buckets).map fun index =>
              choose (binary .wordEq bucket (number index)) (binary .wordOr mask bit)
                (part index buckets seen))))
            (success (boolean false)))
         (recurse seen))
      (recurse seen)
  return .matchData WordMapping.dataType (LanguageResult.resultType .bool) (.first (.var 0))
    [(complete (constant (.second (.var 1)))) 0, step 0]

/-- Compare every byte in the image; bytes beyond the image are ignored only
when `allowSuffix` is true. Missing entries are zero and the first duplicate
key wins, exactly as in packed memory reads. Inputs evaluate once. -/
def compareBytes (bytes : List UInt8) (memory size : Core.Expr) (allowSuffix : Bool := false) : Core.Expr :=
  let buckets := (((bytes.length + 31) / 32) + 255) / 256
  let masksType := bundleType (List.replicate buckets .word)
  (bind (constant (.pair memory size)) fun input =>
    let compare : Code := fun depth => WordMapping.runHelper (.product WordMapping.type masksType) .bool
      (compareBody bytes) (.pair (part 0 2 input depth) (bundle (List.replicate buckets (.word Word.zero))))
    choose (if allowSuffix then binary .wordGt (number bytes.length) (part 1 2 input)
      else binary .wordEq (part 1 2 input) (number bytes.length))
      (if allowSuffix then success (boolean false) else compare)
      (if allowSuffix then compare else success (boolean false))) 0

end Solcore.Frontend.RustHull.ImageComparison
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ObjectLinking
/-! Resolve object symbols before lowering Yul string literals to EVM words.
Symbol names are arbitrary strings and belong to a section-local namespace.
Lexical Yul functions can shadow intrinsic names. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ObjectLinking

private def decodeChars : List Char → Option (List Char)
  | [] => some []
  | '\\' :: escaped :: rest => do
      let char ← match escaped with
        | '"' => some '"' | '\\' => some '\\' | 'n' => some '\n' | 't' => some '\t'
        | _ => none
      return char :: (← decodeChars rest)
  | '\\' :: [] | '"' :: _ => none
  | char :: rest => return char :: (← decodeChars rest)

private def symbolText (expression : YulExpr) : LowerM String := do
  let .literal (.string text) := expression.kind | fail "object symbol must be a string literal" expression.span
  let '"' :: rest := text.toList | fail "object symbol is missing its opening quote" expression.span
  let '"' :: inner := rest.reverse | fail "object symbol is missing its closing quote" expression.span
  match decodeChars inner.reverse with
  | some chars => pure (String.ofList chars)
  | none => fail "invalid object symbol string" expression.span

private def expression : Nat → CodeImage.Image → List String → YulExpr → LowerM YulExpr
  | 0, _, _, value => fail "object symbol expression depth exhausted" value.span
  | fuel + 1, image, functions, value => do
      match value.kind with
      | .call name args =>
          if (name.name = "datasize" || name.name = "dataoffset") && !functions.contains name.name then
            let [argument] := args | fail "object symbol intrinsic requires one argument" value.span
            let symbol ← symbolText argument
            let extent ← (CodeImage.resolve image symbol).mapError fun message => ⟨message, value.span⟩
            let number := if name.name = "datasize" then extent.size else extent.offset
            pure {value with kind := .literal (.number (toString number))}
          else
            return {value with kind := .call name (← args.mapM (expression fuel image functions))}
      | _ => pure value

private def yulStatements : Nat → CodeImage.Image → List String → List YulStmt → LowerM (List YulStmt)
  | 0, _, _, _ => fail "object symbol Yul statement depth exhausted"
  | fuel + 1, image, functions, body => do
      let functions := (body.filterMap fun statement => match statement.kind with
        | .functionDef name _ _ _ => some name.name
        | _ => none) ++ functions
      body.mapM fun statement => do
        let kind : YulStmtKind ← match statement.kind with
          | .block body => YulStmtKind.block <$> yulStatements fuel image functions body
          | .letDecl names init => YulStmtKind.letDecl names <$> init.mapM (expression fuel image functions)
          | .assign names value => YulStmtKind.assign names <$> expression fuel image functions value
          | .expression value => YulStmtKind.expression <$> expression fuel image functions value
          | .ifThen cond body => do
              let cond ← expression fuel image functions cond
              let body ← yulStatements fuel image functions body
              pure (.ifThen cond body)
          | .forLoop init cond post body => do
              -- Initializer functions remain visible throughout the loop.
              let loopFunctions := (init.filterMap fun statement => match statement.kind with
                | .functionDef name _ _ _ => some name.name
                | _ => none) ++ functions
              let init ← yulStatements fuel image functions init
              let cond ← expression fuel image loopFunctions cond
              let post ← yulStatements fuel image loopFunctions post
              let body ← yulStatements fuel image loopFunctions body
              pure (.forLoop init cond post body)
          | .switch value cases defaultBody => do
              let cases ← cases.mapM fun arm => do
                let body ← yulStatements fuel image functions arm.body
                pure {arm with body}
              let value ← expression fuel image functions value
              let defaultBody ← defaultBody.mapM (yulStatements fuel image functions)
              pure (.switch value cases defaultBody)
          | .functionDef name params rets body =>
              YulStmtKind.functionDef name params rets <$> yulStatements fuel image functions body
          | .leave => pure .leave
          | .breakStmt => pure .breakStmt
          | .continueStmt => pure .continueStmt
        pure {statement with kind}

private def statements : Nat → CodeImage.Image → List Stmt → LowerM (List Stmt)
  | 0, _, _ => fail "object symbol Hull statement depth exhausted"
  | fuel + 1, image, body => body.mapM fun statement => do
      let kind : StmtKind ← match statement.kind with
        | .assembly body => StmtKind.assembly <$> yulStatements fuel image [] body
        | .block body => StmtKind.block <$> statements fuel image body
        | .forLoop init cond post body => do
            let init ← statements fuel image init
            let post ← statements fuel image post
            let body ← statements fuel image body
            pure (.forLoop init cond post body)
        | .matchStmt target scrutinee alts => do
            let alts ← alts.mapM fun arm => do
              let body ← statements fuel image arm.body
              pure {arm with body}
            pure (.matchStmt target scrutinee alts)
        | other => pure other
      pure {statement with kind}

private def function (fuel : Nat) (image : CodeImage.Image) (value : Function) : LowerM Function := do
  return {value with body := (← statements fuel image value.body)}

private def objects : Nat → CodeImage.Image → List String → List Object → LowerM (List Object)
  | 0, _, _, _ => fail "object symbol path depth exhausted"
  | fuel + 1, image, path, values => values.mapM fun value => do
      let .object name code children span := value
      match path with
      | [] => fail "object symbol path must not be empty"
      | current :: rest =>
          if current != name then pure value
          else if rest.isEmpty then do
            let stmts ← statements fuel image code.stmts
            let functions ← code.functions.mapM (function fuel image)
            let code := {code with stmts, functions}
            pure (.object name code children span)
          else
            return .object name code (← objects fuel image rest children) span

/-- Resolve the selected section and its shared functions. Validate the complete
image inventory before calling this function; other object sections keep their
own symbol namespaces and remain unchanged. -/
def link (program : Program) (image : CodeImage.Image) (fuel : Nat := 4096) : LowerM Program := do
  let functions ← program.functions.mapM (function fuel image)
  let objects ← objects fuel image image.path program.objects
  return {program with functions, objects}

end Solcore.Frontend.RustHull.ObjectLinking
end
