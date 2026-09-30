import Solcore.Frontend.SourceCoreDataValues

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.RuntimeValue

set_option autoImplicit false

namespace Tests.SourceCoreDataValues

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceInference (DataConstructorInstantiation)
open SourceCoreDataValues

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "enum Packet<T> { Empty, Only(T), Many(T, Bool, Word) }",
    "function identity(value: Word) returns (Word) { return value; }"
  ] }] }

private def dataSignature (program : CheckedProgram) (name : String) : IO ProgramDataSignature :=
  match program.signatures.dataTypes.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"data values signature missing: {name}")

private def instantiation (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty) (name : String) :
    IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors.filter (·.name == name) with
    | [constructor] => pure constructor
    | _ => throw (IO.userError s!"data values constructor missing: {name}")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure {
    constructor := constructor.id
    parameterSubstitution := substitution
    payloadTypes := constructor.payloadTypes.map substitution.apply
    resultType := TypeSystem.Ty.nominal signature.id arguments
  }

private def encoded (context : Context) (type : TypeSystem.Ty) (value : Value) (fuel : Nat := 400) : IO Core.Value :=
  match encode fuel context type value with
  | .ok core => pure core
  | .error error => throw (IO.userError s!"source value encoding failed: {reprStr error}")
private def decoded (context : Context) (type : TypeSystem.Ty) (core : Core.Value) (fuel : Nat := 400) : IO Value :=
  match decode fuel context type core with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"source value decoding failed: {reprStr error}")
private def rejectedEncode (context : Context) (type : TypeSystem.Ty) (value : Value) (fuel : Nat := 400) : IO Error :=
  match encode fuel context type value with
  | .error error => pure error
  | .ok core => throw (IO.userError s!"forged source value accepted: {reprStr core}")
private def rejectedDecode (context : Context) (type : TypeSystem.Ty) (value : Core.Value) (fuel : Nat := 400) : IO Error :=
  match decode fuel context type value with
  | .error error => pure error
  | .ok source => throw (IO.userError s!"forged raw Core value accepted: {reprStr source}")
private def roundtrip (context : Context) (type : TypeSystem.Ty) (value : Value) : IO Core.Value := do
  let core ← encoded context type value
  assertTrue ((← decoded context type core) == value) "source roundtrip changed deep value or metadata"
  assertTrue ((← encoded context type (← decoded context type core)) == core) "Core roundtrip changed complete data tree"
  pure core

private def orderedCore (identity : Core.DataTypeId) : List (Core.Value × Core.Value) → Core.Value
  | [] => .constructed ⟨identity, 0⟩ .unit
  | (key, value) :: rest => .constructed ⟨identity, 1⟩ (.pair (.pair key value) (orderedCore identity rest))

private def recursiveTree (leaf pair : DataConstructorInstantiation) : Nat → Value
  | 0 => .constructed leaf [.integer 7]
  | depth + 1 => .constructed pair [recursiveTree leaf pair depth, .constructed leaf [.integer (-(Int.ofNat depth))]]

example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value} {core : Core.Value}
    (accepted : encode fuel context type value = .ok core) :
    decode fuel context type core = .ok value := decode_encode accepted
example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value} {core : Core.Value}
    (accepted : decode fuel context type core = .ok value) :
    encode fuel context type value = .ok core := encode_decode accepted
example {fuel : Nat} {context : Context} {type : TypeSystem.Ty} {value : Value} {core : Core.Value}
    (accepted : encode fuel context type value = .ok core) :
    ∃ projected, context.checked.catalog.project type = .ok projected ∧
      ∀ world, Core.RuntimeValueHasType world core projected context.checked.catalog.definitions := encode_typed accepted
example {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {metadata : DataConstructorInstantiation} {tag : Core.ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) :
    catalog.constructor? metadata = some tag ∧
      ∃ payload, catalog.definitions.lookupConstructorPayloadType? tag = some payload := resolveConstructor_facts accepted

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"data values fixture failed: {reprStr errors}")
  let tree ← dataSignature program "Tree"
  let packet ← dataSignature program "Packet"
  let treeType := TypeSystem.Ty.nominal tree.id [.integer]
  let wordTree := TypeSystem.Ty.nominal tree.id [.word]
  let stagedTree := TypeSystem.Ty.nominal tree.id [.comptime .word]
  let packetType := TypeSystem.Ty.nominal packet.id [.integer]
  let mapType := TypeSystem.Ty.mapping .integer treeType
  let nestedMap := TypeSystem.Ty.mapping (.proxy (.comptime .word)) mapType
  let functionType := TypeSystem.Ty.function .word .word
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 160
      [treeType, wordTree, stagedTree, packetType, mapType, nestedMap,
        .proxy .word, .proxy (.comptime .word), .proxy functionType, .mapping functionType treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"data values catalog failed: {reprStr error}")
  let context : Context := { checked, signatures := program.signatures }
  let leaf ← instantiation tree [.integer] "Leaf"
  let pair ← instantiation tree [.integer] "Pair"
  let wordLeaf ← instantiation tree [.word] "Leaf"
  let stagedLeaf ← instantiation tree [.comptime .word] "Leaf"
  let empty ← instantiation packet [.integer] "Empty"
  let only ← instantiation packet [.integer] "Only"
  let many ← instantiation packet [.integer] "Many"
  let leafTag ← match checked.catalog.resolveConstructor program.signatures leaf with
    | .ok tag => pure tag | .error error => throw (IO.userError s!"Leaf tag missing: {reprStr error}")
  let pairTag ← match checked.catalog.resolveConstructor program.signatures pair with
    | .ok tag => pure tag | .error error => throw (IO.userError s!"Pair tag missing: {reprStr error}")
  let mapIdentity := (checked.catalog.identity? mapType).getD ⟨999⟩
  let treeValue := Value.constructed pair [
    .constructed leaf [.integer (2 ^ 400)], .constructed leaf [.integer (-8)]]
  let treeCore := Core.Value.constructed pairTag (.pair
    (.constructed leafTag (.integer (2 ^ 400))) (.constructed leafTag (.integer (-8))))
  assertTrue ((← roundtrip context treeType treeValue) == treeCore) "nominal payload order or native Integer changed"
  discard <| roundtrip context packetType (.constructed empty [])
  discard <| roundtrip context packetType (.constructed only [.integer (-55)])
  let manyValue := Value.constructed many [.integer (-10), .bool true, .word Core.Word.zero]
  let manyCore ← roundtrip context packetType manyValue
  match manyCore with
  | .constructed _ (.pair (.integer (-10)) (.pair (.bool true) (.word value))) =>
      assertTrue (value == Core.Word.zero) "many payload Word changed"
  | _ => throw (IO.userError "zero/single/many nominal payload convention changed")
  discard <| roundtrip context wordTree (.constructed wordLeaf [.word Core.Word.zero])
  discard <| roundtrip context stagedTree (.constructed stagedLeaf [.word Core.Word.zero])
  assertTrue (checked.catalog.identity? wordTree != checked.catalog.identity? stagedTree)
    "nominal raw argument staging identity collapsed"

  let mapEntries : List (Value × Value) := [
    (.integer 9, treeValue), (.integer 9, .constructed leaf [.integer 2]),
    (.integer (-1), .constructed leaf [.integer 3])]
  let mapping := Value.mapping .integer treeType mapEntries
  let mappingCore ← roundtrip context mapType mapping
  assertTrue (mappingCore == orderedCore mapIdentity [
    (.integer 9, treeCore), (.integer 9, .constructed leafTag (.integer 2)),
    (.integer (-1), .constructed leafTag (.integer 3))]) "mapping keys were sorted, deduplicated, or reordered"
  let reversed ← encoded context mapType (.mapping .integer treeType mapEntries.reverse)
  assertTrue (mappingCore != reversed) "ordered mapping encoding lost list order"
  discard <| roundtrip context mapType (.mapping .integer treeType [])
  let proxy := Value.proxy (.comptime .word)
  discard <| roundtrip context nestedMap (.mapping (.proxy (.comptime .word)) mapType [(proxy, mapping)])
  let plainProxy ← roundtrip context (.proxy .word) (.proxy .word)
  let stagedProxy ← roundtrip context (.proxy (.comptime .word)) proxy
  assertTrue (plainProxy != stagedProxy) "proxy raw inner staging identity was erased"
  discard <| roundtrip context (.proxy functionType) (.proxy functionType)
  discard <| roundtrip context (.mapping functionType treeType) (.mapping functionType treeType [])

  let scalars := Value.product .unit (.product (.bool true) (.product (.word Core.Word.zero) (.integer (-(2 ^ 512)))))
  let scalarType : TypeSystem.Ty := .product .unit (.product .bool (.product .word .integer))
  discard <| roundtrip context scalarType scalars
  let stagedScalarType : TypeSystem.Ty := .comptime (.product (.comptime .unit)
    (.product .bool (.product (.comptime .word) (.comptime .integer))))
  assertTrue ((← roundtrip context stagedScalarType scalars) == (← encoded context scalarType scalars))
    "runtime staging wrapper projection changed scalar data"
  assertTrue ((← roundtrip context (.comptime treeType) treeValue) == treeCore)
    "outer nominal staging wrapper changed representation"
  let stagedMapType := TypeSystem.Ty.mapping (.comptime .integer) treeType
  assertTrue ((← roundtrip context stagedMapType (.mapping (.comptime .integer) treeType mapEntries)) == mappingCore)
    "mapping payload runtime projection changed"

  for forged in [
      { leaf with parameterSubstitution := [] },
      { leaf with parameterSubstitution := leaf.parameterSubstitution ++ leaf.parameterSubstitution },
      { leaf with parameterSubstitution := leaf.parameterSubstitution.map fun (id, _) => (id, TypeSystem.Ty.bool) },
      { leaf with payloadTypes := [.bool] },
      { leaf with payloadTypes := [] },
      { leaf with resultType := wordTree },
      { leaf with constructor := { leaf.constructor with constructorIndex := 99 } },
      { leaf with constructor := { leaf.constructor with dataType := packet.id } }] do
    discard <| rejectedEncode context treeType (.constructed forged [.integer 7])
  let arity ← rejectedEncode context treeType (.constructed leaf [.integer 1, .integer 2])
  assertTrue (decide (arity.code = .payloadCountMismatch 1 2)) "nominal payload arity error was hidden"
  let deep ← rejectedEncode context treeType (.constructed pair [
    .constructed leaf [.integer 1], .constructed leaf [.bool false]])
  assertTrue (decide (deep.path = [.constructorPayload 1, .constructorPayload 0]))
    "deep source payload path was lost"
  discard <| rejectedEncode context mapType (.mapping .word treeType [])
  discard <| rejectedEncode context mapType (.mapping .integer wordTree [])
  discard <| rejectedEncode context mapType (.mapping .integer treeType [(.bool false, treeValue)])
  discard <| rejectedEncode context (.proxy (.comptime .word)) (.proxy .word)
  discard <| rejectedDecode context (.proxy (.comptime .word)) plainProxy
  discard <| rejectedDecode context (.proxy .word) stagedProxy

  let foreignSignatures : Context := { context with
    signatures := { program.signatures with dataTypes := tree :: program.signatures.dataTypes } }
  discard <| rejectedEncode foreignSignatures treeType treeValue
  discard <| rejectedDecode foreignSignatures treeType treeCore
  let tamperedTree := { tree with constructors := tree.constructors.map fun constructor =>
    if constructor.id = leaf.constructor then { constructor with payloadTypes := [.bool] } else constructor }
  let altered : Context := { context with
    signatures := { program.signatures with dataTypes := tamperedTree :: program.signatures.dataTypes.filter (·.id != tree.id) } }
  discard <| rejectedEncode altered treeType (.constructed leaf [.integer 1])
  discard <| rejectedDecode altered treeType (.constructed leafTag (.integer 1))

  let capabilities : List Core.Value := [
    .closure .word .word (.var 0) [], .cellRef .integer 0,
    .cellRef .integer 999, .hostFunction .storageRead]
  for forbidden in capabilities do
    discard <| rejectedDecode context treeType (.constructed leafTag forbidden)
    discard <| rejectedDecode context (.product .unit treeType) (.pair .unit (.constructed leafTag forbidden))
  discard <| rejectedDecode context treeType (.constructed ⟨leafTag.owner, 999⟩ .unit)
  discard <| rejectedDecode context treeType (.constructed pairTag (.pair (.constructed leafTag (.integer 0)) plainProxy))
  discard <| rejectedDecode context treeType (.inRight .unit treeCore)
  discard <| rejectedDecode context mapType (.constructed ⟨mapIdentity, 1⟩
    (.pair (.pair (.integer 0) treeCore) treeCore))
  discard <| rejectedDecode context mapType (.constructed ⟨mapIdentity, 0⟩ (.integer 0))
  discard <| rejectedDecode context (.proxy .word) (.constructed ⟨(checked.catalog.identity? (.proxy .word)).getD ⟨999⟩, 0⟩
    (.hostFunction .storageRead))
  let functionError ← rejectedEncode context functionType .unit
  assertTrue (decide (functionError.code = .functionHandleRequired)) "source function handle rejection was not explicit"
  let rawFunction := Core.Value.pair (.inRight .unit (.word Core.Word.zero))
    (.closure .word (Core.LanguageResult.resultType .word) (Core.LanguageResult.success (.var 0)) [])
  let functionError ← rejectedDecode context functionType rawFunction
  assertTrue (decide (functionError.code = .functionHandleRequired)) "raw closure passed as a public function handle"
  let referenceError ← rejectedDecode context treeType (.constructed leafTag (.cellRef .integer 999))
  assertTrue (decide (referenceError.code = .externalReferenceUnsupported)) "forged reference category was lost"
  assertTrue (decide (referenceError.path = [.rawCore .constructorPayload])) "deep raw reference path was lost"

  let recursive := recursiveTree leaf pair 25
  discard <| roundtrip context treeType recursive
  discard <| rejectedEncode context treeType recursive 8
  let recursiveCore ← encoded context treeType recursive
  discard <| rejectedDecode context treeType recursiveCore 8
  discard <| rejectedEncode context .integer (.integer 0) 0
  discard <| rejectedDecode context .integer (.integer 0) 0
  IO.println "source Core data values GREEN"

end Tests.SourceCoreDataValues
