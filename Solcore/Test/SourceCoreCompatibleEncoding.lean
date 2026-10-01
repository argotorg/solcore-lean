import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleValues.Encoded.mk

/-! Real checked signatures and public compatible encoding instantiate the
closed independent representation theorem, including raw aliases, recursive
nominal/mapping nesting, duplicates, and transported defaults. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleEncoding
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatibleEncoding CompatiblePayload

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Branch(Tree<T>, Tree<T>) }",
    "function main() returns (Word) { return 7; }"
  ] }] }
private def metadata (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat) : IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "encoding fixture constructor missing")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure ⟨constructor.id, substitution, constructor.payloadTypes.map substitution.apply, .nominal signature.id arguments⟩

private structure Verified (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty)
    (carrier : PublicValue) (source : Dynamic.Value) where
  encoded : SourceCoreCompatibleValues.Encoded 500 context type carrier
  independent : ValueRep context.checked encoded.context.registry (noFunctions context.checked.catalog) [] [] type
    source encoded.value encoded.type

private def verify (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty)
    (carrier : PublicValue) (source : Dynamic.Value) (meaning : Means carrier source) :
    IO (Verified context type carrier source) := do
  match accepted : SourceCoreCompatibleValues.encode 500 context type carrier with
  | .error error => throw (IO.userError s!"independent compatible encoding failed: {reprStr error}")
  | .ok encoded =>
    have independent := encode_represents_at (functions := noFunctions context.checked.catalog) accepted meaning [] []
    have _nativeTyped : RuntimeValueHasType [] encoded.value encoded.type context.checked.catalog.definitions := independent.runtime_hasType
    match SourceCoreCompatibleValues.decode 500 encoded.context type encoded.value with
    | .ok reversed => assertTrue (reversed == carrier) "raw metadata/order changed in public reverse image"
    | .error error => throw (IO.userError s!"encoded reverse image rejected: {reprStr error}")
    match SourceCoreCompatibleValues.decodeCertified 500 encoded.context type encoded.value with
    | .error error => throw (IO.userError s!"certified reverse image rejected: {reprStr error}")
    | .ok decoded =>
      have _extendedMeaning := decoded_represents_extended (context := encoded.context) (functions := noFunctions encoded.context.checked.catalog) decoded [] []
      pure ()
    pure ⟨encoded, independent⟩

private def carrierTree (leaf branch : DataConstructorInstantiation) (payload : PublicValue) : Nat → PublicValue
  | 0 => .constructed leaf [payload]
  | depth + 1 => .constructed branch [carrierTree leaf branch payload depth, carrierTree leaf branch payload 0]
private def sourceTree (leaf branch : DataConstructorInstantiation) (payload : Dynamic.Value) : Nat → Dynamic.Value
  | 0 => .constructed leaf [payload]
  | depth + 1 => .constructed branch [sourceTree leaf branch payload depth, sourceTree leaf branch payload 0]
private theorem treeMeans (leaf branch : DataConstructorInstantiation) {carrier : PublicValue} {source : Dynamic.Value}
    (related : Means carrier source) (depth : Nat) : Means (carrierTree leaf branch carrier depth) (sourceTree leaf branch source depth) := by
  induction depth with
  | zero => simpa only [carrierTree, sourceTree] using (DataPayloadEncoding.Means.constructed (metadata := leaf) (.cons related .nil))
  | succ depth ih => simpa only [carrierTree, sourceTree] using
    (DataPayloadEncoding.Means.constructed (metadata := branch)
      (.cons ih (.cons (.constructed (metadata := leaf) (.cons related .nil)) .nil)))

/-- The public encoding theorem is independent of chosen source metadata;
metadata authenticity is obtained from the accepted codec computation. -/
example {fuel : Nat} {context : SourceCoreCompatibleValues.Context} {type : TypeSystem.Ty}
    {carrier : PublicValue} {source : Dynamic.Value}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context type carrier}
    (accepted : SourceCoreCompatibleValues.encode fuel context type carrier = .ok encoded)
    (meaning : Means carrier source) (world : StoreTyping) :
    ValueRep context.checked encoded.context.registry (noFunctions context.checked.catalog) [] world
      type source encoded.value encoded.type := encode_represents_at accepted meaning [] world

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"encoder source checking failed: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [signature] => pure signature
    | _ => throw (IO.userError "encoder Tree signature missing")
  let proxy : TypeSystem.Ty := .proxy .word
  let rawProxy : TypeSystem.Ty := .proxy (.comptime .word)
  let table : TypeSystem.Ty := .mapping .word proxy
  let rawTable : TypeSystem.Ty := .mapping .word rawProxy
  let treeType : TypeSystem.Ty := .nominal tree.id [table]
  let rawTreeType : TypeSystem.Ty := .nominal tree.id [rawTable]
  let rootType : TypeSystem.Ty := .mapping .word treeType
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 300
      [rootType, .mapping .word table, .function .word .word] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"encoder catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let leaf ← metadata tree [rawTable] 0
  let branch ← metadata tree [rawTable] 1
  let one := Word.ofNatModulo 1
  let rawCarrier : PublicValue := .mapping .word rawProxy [(.word one, .proxy (.comptime .word)), (.word one, .proxy .word)]
  let rawSource : Dynamic.Value := .mapping .word rawProxy [(.word one, .proxy (.comptime .word)), (.word one, .proxy .word)]
  have rawMeans : Means rawCarrier rawSource := .mapping (.prepend (.word _) (.proxy _) (.prepend (.word _) (.proxy _) .empty))
  let raw ← verify context table rawCarrier rawSource rawMeans
  have _shape := raw.independent.mapping_shape rfl
  match raw.encoded.value with
  | .pair (.word header) (.pair (.inRight .unit (.constructed _ (.word defaultId))) _) =>
    assertTrue (raw.encoded.context.registry.lookup header == some (.mapping .word rawProxy)) "raw header canonicalized"
    assertTrue (raw.encoded.context.registry.lookup defaultId == some (.proxy (.comptime .word))) "raw default canonicalized"
  | _ => throw (IO.userError "encoded mapping/default shape changed")
  let recursiveCarrier := carrierTree leaf branch rawCarrier 4
  let recursiveSource := sourceTree leaf branch rawSource 4
  let roots : PublicValue := .mapping .word rawTreeType [(.word one, recursiveCarrier), (.word one, carrierTree leaf branch rawCarrier 0)]
  let sourceRoots : Dynamic.Value := .mapping .word rawTreeType [(.word one, recursiveSource), (.word one, sourceTree leaf branch rawSource 0)]
  have rootMeans : Means roots sourceRoots := .mapping (.prepend (.word _) (treeMeans _ _ rawMeans 4)
    (.prepend (.word _) (treeMeans _ _ rawMeans 0) .empty))
  let nested ← verify raw.encoded.context rootType roots sourceRoots rootMeans
  have _nestedShape := nested.independent.mapping_shape rfl
  match nested.encoded.value with
  | .pair (.word header) (.pair (.inLeft _ .unit) (.constructed _ (.pair (.pair (.word first) _) (.constructed _ (.pair (.pair (.word second) _) (.constructed _ .unit)))))) =>
    assertTrue (first == one && second == one) "duplicate source entries collapsed or reordered"
    assertTrue (nested.encoded.context.registry.lookup header == some (.mapping .word rawTreeType)) "raw nominal mapping header erased"
  | _ => throw (IO.userError "nominal fallback absence or duplicate entry shape changed")
  let nestedDefaultCarrier : PublicValue := .mapping .word rawTable []
  let nestedDefaultSource : Dynamic.Value := .mapping .word rawTable []
  let fallback ← verify nested.encoded.context (.mapping .word table) nestedDefaultCarrier nestedDefaultSource (.mapping .empty)
  match fallback.encoded.value with
  | .pair _ (.pair (.inRight .unit (.pair (.word header) (.pair (.inRight .unit (.constructed _ (.word proxyId))) _))) _) =>
    assertTrue (fallback.encoded.context.registry.lookup header == some (.mapping .word rawProxy)) "nested default header changed"
    assertTrue (fallback.encoded.context.registry.lookup proxyId == some (.proxy (.comptime .word))) "nested default proxy metadata changed"
  | _ => throw (IO.userError "nested transported default shape changed")
  match SourceCoreCompatibleValues.encode 500 context (.function .word .word) .unit with
  | .error error => assertTrue (error.code == .functionHandleRequired) "function data boundary changed"
  | .ok _ => throw (IO.userError "data encoder accepted function payload")
  let forged : PublicValue := .constructed {leaf with payloadTypes := [.bool]} [.bool true]
  match SourceCoreCompatibleValues.encode 500 context treeType forged with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "encoder accepted forged nominal metadata")
  IO.println "actual compatible encoder to independent payload proof GREEN"

end Tests.SourceCoreCompatibleEncoding
