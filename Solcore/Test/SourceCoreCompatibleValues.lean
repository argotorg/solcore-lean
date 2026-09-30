import Solcore.Frontend.SourceCoreCompatibleValues
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleValues.Encoded.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleValues.Decoded.mk

/-! This separate compatibility profile authenticates raw metadata without
erasing it. Its executable data boundary and ordinary Core mapping operations
are tested here; compiler routing, function handles and initial source heaps
are outside this unit. -/

set_option autoImplicit false

namespace Tests.SourceCoreCompatibleValues
open Solcore Solcore.Frontend
open Solcore.Frontend.SourceInference (DataConstructorInstantiation)
open SourceCoreCompatibleValues

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "enum Tree<T> { Leaf(T), Branch(Tree<T>, Tree<T>) }",
    "enum Packet<T> { Empty, Only(T), Many(T, Bool, Word) }",
    "function main() returns (Word) { return 7; }"
  ] }] }

private def data (program : CheckedProgram) (name : String) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"compatible signature missing: {name}")

private def metadata (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat := 0) : IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "compatible constructor missing")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure ⟨constructor.id, substitution, constructor.payloadTypes.map substitution.apply,
    .nominal signature.id arguments⟩

private def encoded (context : Context) (type : TypeSystem.Ty) (value : Value) :
    IO (Encoded 400 context type value) :=
  match encode 400 context type value with
  | .ok receipt => pure receipt
  | .error error => throw (IO.userError s!"compatible encoding failed: {reprStr error}")

private def roundtrip (context : Context) (type : TypeSystem.Ty) (value : Value) :
    IO (Encoded 400 context type value) := do
  let receipt ← encoded context type value
  match decode 400 receipt.context type receipt.value with
  | .ok actual => assertTrue (actual == value) "compatible roundtrip changed raw source data"
  | .error error => throw (IO.userError s!"compatible decoding failed: {reprStr error}")
  let repeated ← encoded receipt.context type value
  assertTrue (repeated.value == receipt.value && repeated.context.registry.length == receipt.context.registry.length)
    "compatible reencoding changed native data or assigned another metadata slot"
  pure receipt

private def rejectDecode (context : Context) (type : TypeSystem.Ty) (core : Core.Value) : IO Error :=
  match decode 400 context type core with
  | .error error => pure error
  | .ok source => throw (IO.userError s!"forged compatible input accepted: {reprStr source}")

private def rejectEncode (context : Context) (type : TypeSystem.Ty) (value : Value) : IO Error :=
  match encode 400 context type value with
  | .error error => pure error
  | .ok _ => throw (IO.userError "forged compatible source metadata accepted")

private def quote : Core.Value → Option Core.Expr
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .pair left right => do pure (.pair (← quote left) (← quote right))
  | .inLeft type value => do pure (.inLeft type (← quote value))
  | .inRight type value => do pure (.inRight type (← quote value))
  | .constructed constructor value => do pure (.construct constructor (← quote value))
  | _ => none

private def literal (value : Core.Value) : IO Core.Expr :=
  match quote value with
  | some expression => pure expression
  | none => throw (IO.userError "compatible test literal contains a capability")

private def completes (definitions : Core.DataEnvironment) (type : Core.Ty) (body : Core.Expr)
    (expected : Core.Value) : IO Unit := do
  let program : Core.Program := ⟨type, body, definitions⟩
  assertTrue program.check "compatible mapping program failed Core checking"
  match program.runStateful 10000 with
  | .done actual _ => assertTrue (actual == expected) s!"compatible Core result changed: {reprStr actual}"
  | result => throw (IO.userError s!"compatible mapping program failed: {reprStr result}")

private def recursive (leaf branch : DataConstructorInstantiation) : Nat → Value
  | 0 => .constructed leaf [.integer (-(2 ^ 400))]
  | depth + 1 => .constructed branch [recursive leaf branch depth, .constructed leaf [.integer (Int.ofNat depth)]]

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value}
    (receipt : Encoded fuel context type value) :
    decode fuel receipt.context type receipt.value = .ok value := receipt.decode_encode

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value}
    (receipt : Encoded fuel context type value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world receipt.value receipt.type context.checked.catalog.definitions := receipt.typed world

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {core : Core.Value}
    (receipt : Decoded fuel context type core) :
    ∃ rebuilt : Extended context.registry Core.Value,
      encodeRaw fuel context.checked context.registry type receipt.source = .ok rebuilt ∧ rebuilt.value = core :=
  receipt.reencodes

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value}
    (receipt : Encoded fuel context type value) (id : Core.Word) (metadata : Metadata)
    (found : context.registry.lookup id = some metadata) :
    receipt.context.registry.lookup id = some metadata := receipt.preserves.lookup found

example (fuel : Nat) (type : TypeSystem.Ty) :
    defaultValue? fuel type = none ↔ SourceTypedRuntime.defaultValue? fuel type = none :=
  defaultValue?_absent_iff fuel type

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"compatible fixture checking failed: {reprStr error}")
  let box ← data program "Box"
  let tree ← data program "Tree"
  let packet ← data program "Packet"
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let treeType := TypeSystem.Ty.nominal tree.id [.integer]
  let packetType := TypeSystem.Ty.nominal packet.id [.integer]
  let proxyType := TypeSystem.Ty.proxy .word
  let proxyMap := TypeSystem.Ty.mapping proxyType .word
  let defaultMap := TypeSystem.Ty.mapping .word proxyType
  let nominalMap := TypeSystem.Ty.mapping .word boxType
  let nestedMap := TypeSystem.Ty.mapping .word (.mapping .word .word)
  let scalarType : TypeSystem.Ty := .product .unit (.product .bool (.product .word .integer))
  let functionType := TypeSystem.Ty.function .word .word
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 200
      [boxType, treeType, packetType, proxyType, .proxy .bool, proxyMap, defaultMap, nominalMap,
        nestedMap, scalarType, functionType, .proxy functionType, .mapping functionType .word,
        .mapping .word functionType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"compatible catalog preparation failed: {reprStr error}")
  let context := Context.initial checked
  assertTrue (checked.catalog.definitions.isWellFormed) "compatible recursive definitions are not well formed"
  let canonicalBox ← match checked.catalog.project boxType with
    | .ok type => pure type | .error error => throw (IO.userError s!"compatible canonical projection failed: {reprStr error}")
  let stagedBoxType ← match checked.catalog.project (.nominal box.id [.comptime .word]) with
    | .ok type => pure type | .error error => throw (IO.userError s!"compatible staged projection failed: {reprStr error}")
  assertTrue (canonicalBox == stagedBoxType)
    "compatible nominal projection distinguished runtime-equivalent arguments"
  assertTrue (checked.catalog.identity? proxyType == checked.catalog.identity? (.proxy (.comptime .word)))
    "compatible proxy identities are not runtime-type keyed"
  let strict ← match SourceCoreDataCatalog.prepare program.signatures 100 [proxyType, boxType, .nominal box.id [.comptime .word]] with
    | .ok strict => pure strict
    | .error error => throw (IO.userError s!"strict catalog regression preparation failed: {reprStr error}")
  assertTrue (strict.catalog.identity? boxType != strict.catalog.identity? (.nominal box.id [.comptime .word]))
    "separate compatible profile changed strict nominal identity"
  let proxyOwner := (checked.catalog.identity? proxyType).getD ⟨999⟩
  assertTrue (checked.catalog.definitions.lookupConstructorPayloadType? ⟨proxyOwner, 0⟩ == some .word)
    "compatible proxy is missing its raw metadata word"
  let strictProxy := (strict.catalog.identity? proxyType).getD ⟨999⟩
  assertTrue (strict.catalog.definitions.lookupConstructorPayloadType? ⟨strictProxy, 0⟩ == some .unit)
    "strict proxy payload convention changed"

  let scalars : Value := .product .unit (.product (.bool true) (.product (.word (word 17)) (.integer (-(2 ^ 512)))))
  let scalar ← roundtrip context (.comptime scalarType) scalars
  assertTrue (scalar.value == .pair .unit (.pair (.bool true) (.pair (.word (word 17)) (.integer (-(2 ^ 512))))))
    "scalar stage projection or unbounded integer changed"
  let ordinary ← roundtrip scalar.context proxyType (.proxy .word)
  let staged ← roundtrip ordinary.context proxyType (.proxy (.comptime .word))
  assertTrue (ordinary.value != staged.value && staged.context.registry.length == ordinary.context.registry.length + 1)
    "dynamic proxy metadata was erased or not certified as an extension"
  let ordinaryBox ← metadata box [.word]
  let stagedBox ← metadata box [.comptime .word]
  let boxValue ← roundtrip staged.context boxType (.constructed ordinaryBox [.word (word 7)])
  let stagedBoxValue ← roundtrip boxValue.context boxType (.constructed stagedBox [.word (word 7)])
  assertTrue (boxValue.value != stagedBoxValue.value) "nominal raw instantiation metadata collapsed"
  match boxValue.value, stagedBoxValue.value with
  | .constructed left _, .constructed right _ => assertTrue (left == right) "canonical compatible nominal native tag changed"
  | _, _ => throw (IO.userError "compatible nominal metadata was not carried in payloads")
  let leaf ← metadata tree [.integer]
  let branch ← metadata tree [.integer] 1
  let treeValue ← roundtrip stagedBoxValue.context treeType (recursive leaf branch 12)
  let empty ← metadata packet [.integer]
  let only ← metadata packet [.integer] 1
  let many ← metadata packet [.integer] 2
  let packetEmpty ← roundtrip treeValue.context packetType (.constructed empty [])
  let packetOnly ← roundtrip packetEmpty.context packetType (.constructed only [.integer 3])
  let packetMany ← roundtrip packetOnly.context packetType (.constructed many [.integer (-2), .bool true, .word (word 8)])
  let entries : List (Value × Value) := [(.proxy (.comptime .word), .word (word 7)),
    (.proxy (.comptime .word), .word (word 99)), (.proxy .word, .word (word 8))]
  let mapping ← roundtrip packetMany.context proxyMap (.mapping proxyType .word entries)
  let reversed ← roundtrip mapping.context proxyMap (.mapping proxyType .word entries.reverse)
  assertTrue (mapping.value != reversed.value) "compatible mapping sorted or deduplicated entry order"
  let transported ← roundtrip reversed.context defaultMap (.mapping (.comptime .word) (.proxy (.comptime .word)) [])
  let nested ← roundtrip transported.context nestedMap (.mapping .word (.mapping (.comptime .word) (.comptime .word)) [])
  let missing ← roundtrip nested.context nominalMap (.mapping .word boxType [])
  let proxyFunction ← roundtrip missing.context (.proxy functionType) (.proxy functionType)
  let emptyFunctionKeys ← roundtrip proxyFunction.context (.mapping functionType .word) (.mapping functionType .word [])
  let emptyFunctionValues ← roundtrip emptyFunctionKeys.context (.mapping .word functionType) (.mapping .word functionType [])
  let context := emptyFunctionValues.context
  let proxyLayout ← match checked.catalog.mappingLayout proxyType .word with
    | .ok layout => pure layout | .error error => throw (IO.userError s!"compatible proxy layout failed: {reprStr error}")
  let proxyComparator : Core.Expr := .lambda (.product proxyLayout.keyType proxyLayout.keyType) .bool
    (.matchData proxyOwner .bool (.first (.var 0)) [
      .matchData proxyOwner .bool (.second (.var 1)) [.binary .wordEq (.var 1) (.var 0)]])
  let mappingExpression ← literal mapping.value
  let stagedKey ← literal staged.value
  let ordinaryKey ← literal ordinary.value
  completes checked.catalog.definitions (Core.LanguageResult.resultType .word)
    (SourceCoreMappingWithDefault.lookup proxyLayout (word 1000) proxyComparator mappingExpression stagedKey)
    (.inRight .word (.word (word 7)))
  completes checked.catalog.definitions (Core.LanguageResult.resultType .word)
    (SourceCoreMappingWithDefault.lookup proxyLayout (word 1000) proxyComparator mappingExpression ordinaryKey)
    (.inRight .word (.word (word 8)))
  let wordComparator : Core.Expr := .lambda (.product .word .word) .bool
    (.binary .wordEq (.first (.var 0)) (.second (.var 0)))
  let defaultLayout ← match checked.catalog.mappingLayout .word proxyType with
    | .ok layout => pure layout | .error error => throw (IO.userError s!"compatible default layout failed: {reprStr error}")
  completes checked.catalog.definitions (Core.LanguageResult.resultType defaultLayout.valueType)
    (SourceCoreMappingWithDefault.lookup defaultLayout (word 1000) wordComparator (← literal transported.value) (.word (word 4)))
    (.inRight .word staged.value)
  let missingLayout ← match checked.catalog.mappingLayout .word boxType with
    | .ok layout => pure layout | .error error => throw (IO.userError s!"compatible missing layout failed: {reprStr error}")
  let missingHeader ← match missing.value with
    | .pair (.word header) _ => pure header | _ => throw (IO.userError "compatible missing header is malformed")
  completes checked.catalog.definitions (Core.LanguageResult.resultType missingLayout.valueType)
    (SourceCoreMappingWithDefault.lookup missingLayout (word 1000) wordComparator (← literal missing.value) (.word (word 4)))
    (.inLeft missingLayout.valueType (.word ((word 1000).add missingHeader)))

  let changedDefault ← match transported.value with
    | .pair header (.pair _ entries) => pure (.pair header (.pair (.inRight .unit ordinary.value) entries))
    | _ => throw (IO.userError "compatible transported carrier is malformed")
  let tampered ← rejectDecode context defaultMap changedDefault
  assertTrue (tampered.code == .transportedDefaultMismatch) "same-typed forged default was accepted"
  let unknown := Core.Value.constructed ⟨proxyOwner, 0⟩ (.word (word 999999))
  let unknownError ← rejectDecode context proxyType unknown
  assertTrue (unknownError.code == .unknownMetadata (word 999999)) "unknown raw metadata ID accepted"
  let zeroError ← rejectDecode context proxyType (.constructed ⟨proxyOwner, 0⟩ (.word Core.Word.zero))
  assertTrue (zeroError.code == .unknownMetadata Core.Word.zero) "reserved metadata zero was accepted"
  discard <| rejectDecode context proxyType (.constructed ⟨proxyOwner, 1⟩ (.word (word 1)))
  let wrongKind ← match transported.value with
    | .pair header _ => pure (.constructed ⟨proxyOwner, 0⟩ header)
    | _ => throw (IO.userError "compatible mapping header missing")
  discard <| rejectDecode context proxyType wrongKind
  discard <| rejectEncode context boxType (.constructed {stagedBox with payloadTypes := [.bool]} [.bool true])
  discard <| rejectEncode context boxType (.constructed ordinaryBox [])
  discard <| rejectEncode context boxType (.constructed {ordinaryBox with
    parameterSubstitution := ordinaryBox.parameterSubstitution ++ ordinaryBox.parameterSubstitution} [.word (word 7)])
  discard <| rejectEncode context boxType (.constructed ordinaryBox [.bool true])
  discard <| rejectEncode context .word (.bool false)
  discard <| rejectDecode context (.product .word .word) (.pair (.word (word 1)) (.cellRef .word 0))
  discard <| rejectDecode context (.product .word .word) (.pair (.word (word 1)) (.hostFunction .storageRead))
  let nativeBoxForgery ← match boxValue.value with
    | .constructed tag (.pair rawId _) => pure (.constructed tag (.pair rawId (.cellRef .word 0)))
    | _ => throw (IO.userError "compatible Box carrier is malformed")
  discard <| rejectDecode context boxType nativeBoxForgery
  let functionError ← rejectDecode context functionType (.closure .word .word (.var 0) [])
  assertTrue (functionError.code == .functionHandleRequired) "raw closure crossed the data-only compatibility boundary"
  let handleError ← rejectEncode context functionType .unit
  assertTrue (handleError.code == .functionHandleRequired) "function data accepted without an authenticated handle"
  match encode 0 context treeType (recursive leaf branch 0) with
  | .error error => assertTrue (error.code == .exhausted) "codec exhausted with a different error"
  | .ok _ => throw (IO.userError "codec ignored its fuel bound")
  let limited ← match SourceCoreCompatibleCatalog.prepare program.signatures 50 [proxyType] [] {maxEntries := 1} with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"compatible bounded catalog failed: {reprStr error}")
  let budgetError ← rejectEncode (Context.initial limited) proxyType (.proxy (.comptime .word))
  assertTrue (budgetError.code == .metadata (.entryBudgetExhausted 1)) "compatible codec bypassed checked metadata extension budget"
  IO.println "compatible catalog, raw metadata, transported defaults and typed deep codec GREEN"

end Tests.SourceCoreCompatibleValues
