import Solcore.Frontend.RustHull.Syntax
import Solcore.Frontend.RustHull.Memory
import Solcore.Util.Json

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
def backendRevision : String := "8ee24814ea9b32c762df8ef80c796e7d48797c0f"

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
  unless (← text (← field backend "name")) = "sonatina" &&
      (← text (← field backend "revision")) = backendRevision &&
      (← text (← field backend "optimization")) = "O0" do
    throw "unsupported code image backend configuration"
  array decodeImage (← field json "images")

end Solcore.Frontend.RustHull.CodeImage
