import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Encoding
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality

/-!
# Compatible encoding tests

Actual encodings, comparators and mappings.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleEncodedDataTyping
/-! Consumers retain the actual compatible encoder equations and definition
prefix. Negative cases distinguish structural data from annotation validity
and exclude closures, references and newly appended constructor identities.
These are static proof consumers; the existing encoder remains unchanged. -/
set_option autoImplicit false
namespace Solcore.Tests.SourceCoreCompatibleEncodedDataTyping
open Core Frontend SourceSemantics.CoreLowering
open CompatibleEncodedDataTyping

theorem actual_raw_typing {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty}
    {carrier : SourceCoreDataValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Value}
    {world : StoreTyping} {type : Ty} {future : DataEnvironment}
    (accepted : SourceCoreCompatibleValues.encodeRaw fuel checked registry expected carrier = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (extension : checked.catalog.definitions.Extends future)
    (typed : RuntimeValueHasType world encoded.value type future) :
    RuntimeValueHasType world encoded.value type checked.catalog.definitions :=
  encodeRaw_restrict_typing accepted projected extension typed

theorem actual_payloads {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {types : List TypeSystem.Ty}
    {carriers : List SourceCoreDataValues.Value} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : SourceCoreCompatibleValues.encodePayloadsRaw fuel checked registry types carriers index = .ok encoded) :
    DataOnly encoded.value := encodePayloadsRaw_dataOnly accepted

theorem actual_ordered_entries {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    {carriers : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : SourceCoreCompatibleValues.encodeEntriesRaw fuel checked registry key value layout carriers index = .ok encoded) :
    DataOnly encoded.value := encodeEntriesRaw_dataOnly accepted

theorem actual_default {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {sourceType : TypeSystem.Ty} {type : Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : SourceCoreCompatibleValues.encodeDefaultRaw fuel checked registry sourceType type = .ok encoded) :
    DataOnly encoded.value := encodeDefaultRaw_dataOnly accepted

theorem closure_not_data {parameter result : Ty} {body : Expr} {captured : Environment} :
    ¬ DataOnly (.closure parameter result body captured) := by
  intro data
  cases data

theorem reference_not_data {type : Ty} {location : Location} :
    ¬ DataOnly (.cellRef type location) := by
  intro data
  cases data

/-- Runtime sum typing omits the unused annotation check. The prefix theorem
requires the independently projected well formed annotation for this reason. -/
theorem data_runtime_does_not_certify_annotation :
    DataOnly (.inLeft (.namedData ⟨0⟩) .unit) ∧
    RuntimeValueHasType [] (.inLeft (.namedData ⟨0⟩) .unit) (.sum .unit (.namedData ⟨0⟩)) [] ∧
    ¬ Ty.WellFormed [] (.sum .unit (.namedData ⟨0⟩)) := by
  refine ⟨.inLeft .unit, .inLeft .unit, ?_⟩
  intro annotation
  cases annotation with
  | sum _ right => cases right with
    | namedData found => cases found

private def base : DataEnvironment := [⟨[.unit]⟩]
private def suffix : DataEnvironment := [⟨[.word]⟩]
private def firstConstructor : ConstructorId := ⟨⟨0⟩, 0⟩

/-- The appended definition differs from the selected original definition.
The helper recovers the same owner and payload from the real prefix lookup. -/
theorem original_named_payload :
    RuntimeValueHasType [] (.constructed firstConstructor .unit) (.namedData ⟨0⟩) base := by
  apply DataOnly.restrict_definitions (future := base ++ suffix) (.constructed .unit)
    (DataEnvironment.isWellFormed_sound (by decide)) (.append base suffix)
    (.namedData (by rfl))
  exact .constructed (by rfl) .unit

/-- Structural data at a fresh appended owner cannot be cast into an empty
base. The independent projection/prefix annotation is essential. -/
theorem fresh_named_owner_does_not_restrict :
    DataOnly (.constructed firstConstructor .unit) ∧
    RuntimeValueHasType [] (.constructed firstConstructor .unit) (.namedData ⟨0⟩) base ∧
    ¬ RuntimeValueHasType [] (.constructed firstConstructor .unit) (.namedData ⟨0⟩) [] := by
  refine ⟨.constructed .unit, .constructed (by rfl) .unit, ?_⟩
  intro typed
  cases typed with
  | constructed selected _ => cases selected

end Solcore.Tests.SourceCoreCompatibleEncodedDataTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleEncoding
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleEqualityProofs
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked catalogs and actual public encodings consume the whole comparison
proof, including registry extension, aliases and nested recursive mappings.
Callable tests separately expose their required identity authentication law. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleEqualityProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem noIdentities_faithful : DataEquality.IdentityFaithful noIdentities :=
  ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionObservations catalog (noFunctions catalog) noIdentities := fun impossible => False.elim impossible
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Branch(Tree<T>, Tree<T>) }",
    "function main() returns (Word) { return 7; }"
  ]}] }
private def metadata (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty) (index : Nat) : IO DataConstructorInstantiation := do
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor | none => throw (IO.userError "equality fixture constructor missing")
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  pure ⟨constructor.id, substitution, constructor.payloadTypes.map substitution.apply, .nominal signature.id arguments⟩

private def compare (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty)
    (left right : SourceCoreDataValues.Value) (sourceLeft sourceRight : Dynamic.Value)
    (leftMeaning : CompatibleEncoding.Means left sourceLeft) (rightMeaning : CompatibleEncoding.Means right sourceRight)
    (expected : Bool) : IO Unit := do
  let prepared ← match SourceCoreCompatibleDataEquality.prepare 200 context.checked type with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"compatible comparator preparation failed: {reprStr error}")
  match firstAccepted : SourceCoreCompatibleValues.encode 500 context prepared.sourceType left with
  | .error error => throw (IO.userError s!"first equality encode failed: {reprStr error}")
  | .ok first =>
    match secondAccepted : SourceCoreCompatibleValues.encode 500 first.context prepared.sourceType right with
    | .error error => throw (IO.userError s!"second equality encode failed: {reprStr error}")
    | .ok second =>
      let environment := [first.value, second.value]
      let store := [Value.integer (-55)]
      have _wholeProof := encoded_compare_run prepared firstAccepted secondAccepted leftMeaning rightMeaning
        noIdentities_faithful (noFunctionObservations context.checked.catalog) [] [] environment store (.var 0) (.var 1)
        (.var rfl) (.var rfl)
      let expression := comparison prepared (.var 0) (.var 1)
      assertTrue (infer? [prepared.type, prepared.type] expression context.checked.catalog.definitions == some .bool)
        "generated compatible comparison rejected by native checker"
      match runStateful 200000 (.initial expression environment store) with
      | .done (.bool result) finalStore =>
        assertTrue (result == expected) "compatible source equality changed"
        assertTrue (finalStore == preparedStore prepared environment store) "comparison mutated existing cells or allocated during recursive comparison"
      | other => throw (IO.userError s!"compatible comparison did not finish: {reprStr other}")
      match runStateful 1 (.initial expression environment store) with
      | .outOfFuel checkpoint =>
        match runStateful 200000 checkpoint with
        | .done (.bool result) finalStore =>
          assertTrue (result == expected && finalStore == preparedStore prepared environment store) "compatible comparison resume changed result/store"
        | other => throw (IO.userError s!"compatible comparison resume failed: {reprStr other}")
      | _ => throw (IO.userError "compatible equality fixture no longer exercises checkpoint resumption")

private def carrierTree (leaf branch : DataConstructorInstantiation) (payload : SourceCoreDataValues.Value) : Nat → SourceCoreDataValues.Value
  | 0 => .constructed leaf [payload]
  | depth + 1 => .constructed branch [carrierTree leaf branch payload depth, carrierTree leaf branch payload 0]
private def sourceTree (leaf branch : DataConstructorInstantiation) (payload : Dynamic.Value) : Nat → Dynamic.Value
  | 0 => .constructed leaf [payload]
  | depth + 1 => .constructed branch [sourceTree leaf branch payload depth, sourceTree leaf branch payload 0]
private theorem treeMeans (leaf branch : DataConstructorInstantiation)
    {carrier : SourceCoreDataValues.Value} {source : Dynamic.Value} (related : CompatibleEncoding.Means carrier source) (depth : Nat) :
    CompatibleEncoding.Means (carrierTree leaf branch carrier depth) (sourceTree leaf branch source depth) := by
  induction depth with
  | zero => simpa only [carrierTree, sourceTree] using (DataPayloadEncoding.Means.constructed (metadata := leaf) (.cons related .nil))
  | succ depth ih => simpa only [carrierTree, sourceTree] using
    (DataPayloadEncoding.Means.constructed (metadata := branch) (.cons ih (.cons (.constructed (metadata := leaf) (.cons related .nil)) .nil)))

/-- Function equality needs faithful identities; it does not inspect closure
code/captures or infer source identity from native typing. -/
example {checked : SourceCoreCompatibleCatalog.Checked} (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : DataEquality.IdentityFaithful identities) (source : Dynamic.Closure) (parameter result : Ty)
    (code : Value) (contract : Word) (profile : checked.catalog.callableContracts = true)
    (type : prepared.type = CallableContract.functionType parameter result) (environment : Environment) (store : Store) :
    ∃ answer, answer = false ∧ Evaluates
      (.pair (.pair (.inLeft .word .unit) code) (.word contract) :: environment) store
      (comparison prepared (.var 0) (.var 0)) (.bool answer)
      (preparedStore prepared (.pair (.pair (.inLeft .word .unit) code) (.word contract) :: environment) store) := by
  have observed : Observation checked.catalog registry identities prepared.type (.closure source)
      (.pair (.pair (.inLeft .word .unit) code) (.word contract)) := by
    rw [type]; exact .contractedAnonymous source parameter result code contract profile
  obtain ⟨answer, meaning, evaluated⟩ := prepared_compare_preserves prepared faithful observed observed
    (.pair (.pair (.inLeft .word .unit) code) (.word contract) :: environment) store (.var 0) (.var 0)
    (.var rfl) (.var rfl)
  refine ⟨answer, ?_, evaluated⟩
  cases answer with
  | false => rfl
  | true => have impossible := (meaning.mp rfl).2; cases impossible

/-- Contract descriptors and closure implementations do not replace the
retained source identity used by equality. -/
example {checked : SourceCoreCompatibleCatalog.Checked} (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : DataEquality.IdentityFaithful identities) {source : Dynamic.Value} {identity : Word}
    (authenticated : identities source identity) (parameter result : Ty) (leftCode rightCode : Value)
    (leftContract rightContract : Word) (profile : checked.catalog.callableContracts = true)
    (type : prepared.type = CallableContract.functionType parameter result) (store : Store) :
    Evaluates [.pair (.pair (.inRight .unit (.word identity)) leftCode) (.word leftContract),
      .pair (.pair (.inRight .unit (.word identity)) rightCode) (.word rightContract)] store
      (comparison prepared (.var 0) (.var 1)) (.bool true)
      (preparedStore prepared [.pair (.pair (.inRight .unit (.word identity)) leftCode) (.word leftContract),
        .pair (.pair (.inRight .unit (.word identity)) rightCode) (.word rightContract)] store) := by
  have left : Observation checked.catalog registry identities prepared.type source
      (.pair (.pair (.inRight .unit (.word identity)) leftCode) (.word leftContract)) := by
    rw [type]; exact .contractedIdentified parameter result leftCode leftContract authenticated profile
  have right : Observation checked.catalog registry identities prepared.type source
      (.pair (.pair (.inRight .unit (.word identity)) rightCode) (.word rightContract)) := by
    rw [type]; exact .contractedIdentified parameter result rightCode rightContract authenticated profile
  obtain ⟨answer, meaning, evaluated⟩ := prepared_compare_preserves prepared faithful left right
    [.pair (.pair (.inRight .unit (.word identity)) leftCode) (.word leftContract),
      .pair (.pair (.inRight .unit (.word identity)) rightCode) (.word rightContract)] store (.var 0) (.var 1) (.var rfl) (.var rfl)
  have same := meaning.mpr ⟨rfl, faithful.comparable authenticated⟩
  simpa only [same] using evaluated

private def compareCallables (checked : SourceCoreCompatibleCatalog.Checked) : IO Unit := do
  let prepared ← match SourceCoreCompatibleDataEquality.prepare 200 checked (.function .word .integer) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"callable equality prepare failed: {reprStr error}")
  let firstCode : Value := .closure .word (.sum .word .integer) (LanguageResult.success (.unary .wordToInteger (.var 0))) []
  let secondCode : Value := .closure .word (.sum .word .integer) (LanguageResult.success (.integer 99)) []
  let identity := Word.ofNatModulo 17
  let first : Value := .pair (.pair (.inRight .unit (.word identity)) firstCode) (.word (Word.ofNatModulo 3))
  let second : Value := .pair (.pair (.inRight .unit (.word identity)) secondCode) (.word (Word.ofNatModulo 8))
  let anonymous : Value := .pair (.pair (.inLeft .word .unit) firstCode) (.word (Word.ofNatModulo 3))
  for (left, right, expected) in [(first, second, true), (anonymous, anonymous, false), (first, anonymous, false), (anonymous, first, false)] do
    let environment := [left, right]
    match runStateful 200000 (.initial (comparison prepared (.var 0) (.var 1)) environment []) with
    | .done (.bool result) store =>
      assertTrue (result == expected && store == preparedStore prepared environment []) "callable identity/anonymous equality changed"
    | other => throw (IO.userError s!"callable equality did not finish: {reprStr other}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"equality source failed: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [signature] => pure signature | _ => throw (IO.userError "equality Tree signature missing")
  let proxy : TypeSystem.Ty := .proxy .word
  let rawProxy : TypeSystem.Ty := .proxy (.comptime .word)
  let table : TypeSystem.Ty := .mapping .word proxy
  let rawTable : TypeSystem.Ty := .mapping .word rawProxy
  let proxyTree : TypeSystem.Ty := .nominal tree.id [proxy]
  let tableTree : TypeSystem.Ty := .nominal tree.id [table]
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 500
      [proxyTree, tableTree, .mapping .word tableTree, .product .integer .word, .function .word .integer] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"equality catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  compare context proxy (.proxy .word) (.proxy .word) (.proxy .word) (.proxy .word) (.proxy _) (.proxy _) true
  compare context proxy (.proxy .word) (.proxy (.comptime .word)) (.proxy .word) (.proxy (.comptime .word)) (.proxy _) (.proxy _) false
  compare context proxy (.proxy (.comptime .word)) (.proxy (.comptime .word)) (.proxy (.comptime .word)) (.proxy (.comptime .word)) (.proxy _) (.proxy _) true
  let one := Word.ofNatModulo 1
  let entries : SourceCoreDataValues.Value := .mapping .word rawProxy [(.word one, .proxy .word), (.word one, .proxy (.comptime .word))]
  let sourceEntries : Dynamic.Value := .mapping .word rawProxy [(.word one, .proxy .word), (.word one, .proxy (.comptime .word))]
  have entryMeans : CompatibleEncoding.Means entries sourceEntries := .mapping (.prepend (.word _) (.proxy _) (.prepend (.word _) (.proxy _) .empty))
  compare context table entries entries sourceEntries sourceEntries entryMeans entryMeans false
  compare context table (.mapping .word proxy []) (.mapping .word rawProxy [])
    (.mapping .word proxy []) (.mapping .word rawProxy []) (.mapping .empty) (.mapping .empty) false
  let plainLeaf ← metadata tree [proxy] 0
  let rawLeaf ← metadata tree [rawProxy] 0
  let rawBranch ← metadata tree [rawProxy] 1
  compare context proxyTree (.constructed plainLeaf [.proxy .word]) (.constructed rawLeaf [.proxy .word])
    (.constructed plainLeaf [.proxy .word]) (.constructed rawLeaf [.proxy .word])
    (.constructed (.cons (.proxy _) .nil)) (.constructed (.cons (.proxy _) .nil)) false
  let recursive := carrierTree rawLeaf rawBranch (.proxy (.comptime .word)) 4
  let sourceRecursive := sourceTree rawLeaf rawBranch (.proxy (.comptime .word)) 4
  compare context proxyTree recursive recursive sourceRecursive sourceRecursive (treeMeans _ _ (.proxy _) 4) (treeMeans _ _ (.proxy _) 4) true
  compare context proxyTree recursive (.constructed rawLeaf [.proxy (.comptime .word)])
    sourceRecursive (.constructed rawLeaf [.proxy (.comptime .word)])
    (treeMeans _ _ (.proxy _) 4) (.constructed (.cons (.proxy _) .nil)) false
  let mapLeaf ← metadata tree [rawTable] 0
  let mapBranch ← metadata tree [rawTable] 1
  let nested := carrierTree mapLeaf mapBranch entries 4
  let sourceNested := sourceTree mapLeaf mapBranch sourceEntries 4
  compare context tableTree nested nested sourceNested sourceNested (treeMeans _ _ entryMeans 4) (treeMeans _ _ entryMeans 4) false
  compare context (.mapping .word tableTree) (.mapping .word tableTree [(.word one, nested), (.word one, nested)])
    (.mapping .word tableTree [(.word one, nested), (.word one, nested)])
    (.mapping .word tableTree [(.word one, sourceNested), (.word one, sourceNested)])
    (.mapping .word tableTree [(.word one, sourceNested), (.word one, sourceNested)])
    (.mapping (.prepend (.word _) (treeMeans _ _ entryMeans 4) (.prepend (.word _) (treeMeans _ _ entryMeans 4) .empty)))
    (.mapping (.prepend (.word _) (treeMeans _ _ entryMeans 4) (.prepend (.word _) (treeMeans _ _ entryMeans 4) .empty))) false
  compare context (.product .integer .word) (.product (.integer (-99)) (.word one)) (.product (.integer (-99)) (.word one))
    (.product (.integer (-99)) (.word one)) (.product (.integer (-99)) (.word one))
    (.product (.integer _) (.word _)) (.product (.integer _) (.word _)) true
  compareCallables checked
  IO.println "compatible equality extraction, finite helper meaning, and reflection GREEN"

end Tests.SourceCoreCompatibleEqualityProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMappingProofs
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual encoding/comparator/place preparation exercises the independent
mapping theorems. Raw aliases and duplicate order remain visible on decode. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMappingProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful noIdentities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionObservations catalog (noFunctions catalog) noIdentities := fun impossible => False.elim impossible
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }", "function main() returns (Word) { return 0; }"
  ]}] }

private def completed (expression : Expr) (environment : Environment) (store : Store) : IO (Value × Store) := do
  let result ← match runStateful 200000 (.initial expression environment store) with
    | .done value finalStore => pure (value, finalStore)
    | other => throw (IO.userError s!"compatible mapping helper did not finish: {reprStr other}")
  match runStateful 1 (.initial expression environment store) with
  | .outOfFuel checkpoint =>
    match runStateful 200000 checkpoint with
    | .done value finalStore => assertTrue (value == result.1 && finalStore == result.2) "mapping helper resume changed value/store"
    | other => throw (IO.userError s!"mapping helper resume failed: {reprStr other}")
  | _ => throw (IO.userError "mapping regression no longer yields a checkpoint")
  assertTrue (result.2[0]? == store[0]?) "mapping helper modified earlier store"
  pure result

private def decoded (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty)
    (native : Value) (expected : SourceCoreDataValues.Value) : IO Unit := do
  match SourceCoreCompatibleValues.decode 500 context type native with
  | .ok actual => assertTrue (actual == expected) "raw mapping metadata/default/ordered entries changed"
  | .error error => throw (IO.userError s!"compatible mapping result decode failed: {reprStr error}")

private def exercise (context : SourceCoreCompatibleValues.Context) (owner : Resolved.DeclarationId)
    (sourceKey sourceValue : TypeSystem.Ty) (carrier keyCarrier replacementCarrier : SourceCoreDataValues.Value)
    (sources : List (Dynamic.Value × Dynamic.Value)) (sourceLookup : Dynamic.Value)
    (mappingMeaning : CompatibleEncoding.Means carrier (.mapping sourceKey sourceValue sources))
    (keyMeaning : CompatibleEncoding.Means keyCarrier sourceLookup)
    (expectedRead : Option SourceCoreDataValues.Value) (expectedInserted : SourceCoreDataValues.Value) : IO Unit := do
  match layoutAccepted : context.checked.catalog.mappingLayout sourceKey sourceValue with
  | .error error => throw (IO.userError s!"mapping layout rejected: {reprStr error}")
  | .ok layout =>
    have facts := CompatibleEncoding.mappingLayout_facts (checked := context.checked) layoutAccepted
    have projection := CompatibleEncoding.mapping_project facts.1 facts.2.1 facts.2.2.1
    match comparisonAccepted : SourceCoreCompatibleDataEquality.prepare 200 context.checked sourceKey with
    | .error error => throw (IO.userError s!"mapping comparator rejected: {reprStr error}")
    | .ok comparison =>
      have comparisonProjection : context.checked.catalog.project sourceKey = .ok comparison.type := by
        simpa only [CompatibleMapping.comparison_sourceType comparisonAccepted] using comparison.projection
      have keyType := Except.ok.inj (facts.2.1.symm.trans comparisonProjection)
      match mappingAccepted : SourceCoreCompatibleValues.encode 500 context (.mapping sourceKey sourceValue) carrier with
      | .error error => throw (IO.userError s!"mapping encoding rejected: {reprStr error}")
      | .ok encodedMapping =>
        match keyAccepted : SourceCoreCompatibleValues.encode 500 encodedMapping.context sourceKey keyCarrier with
        | .error error => throw (IO.userError s!"mapping key encoding rejected: {reprStr error}")
        | .ok encodedKey =>
          let environment := [encodedMapping.value, encodedKey.value]
          let before := [Value.integer (-99)]
          let missing := word 1000
          have _whole := encoded_lookup_run comparison layout facts.2.2.2 keyType projection facts.2.1 mappingAccepted keyAccepted
            mappingMeaning keyMeaning faithful (noFunctionObservations context.checked.catalog) [] [] environment before missing
            (.var 0) (.var 1) (.var rfl) (.var rfl)
          let header ← match encodedMapping.value with
            | .pair (.word header) _ => pure header
            | _ => throw (IO.userError "mapping carrier omitted raw header")
          assertTrue (encodedKey.context.registry.lookup header == some (.mapping sourceKey sourceValue)) "raw header identity erased"
          let lookup := SourceCoreMappingWithDefault.lookup layout missing comparison.expression (.var 0) (.var 1)
          assertTrue (infer? [SourceCoreMappingWithDefault.type layout, layout.keyType] lookup context.checked.catalog.definitions == some (LanguageResult.resultType layout.valueType)) "mapping lookup checker failed"
          let (result, store) ← completed lookup environment before
          assertTrue (store.length == before.length + context.checked.catalog.entries.length + 1) "mapping lookup administrative count changed"
          match expectedRead, result with
          | some expected, .inRight .word value => decoded encodedKey.context sourceValue value expected
          | none, .inLeft _ (.word token) => assertTrue (token == missing.add header) "missing-default raw header token changed"
          | _, _ => throw (IO.userError s!"mapping lookup outcome mismatch: {reprStr result}")
          let encodedReplacement ← match SourceCoreCompatibleValues.encode 500 encodedKey.context sourceValue replacementCarrier with
            | .ok encoded => pure encoded
            | .error error => throw (IO.userError s!"mapping replacement encoding rejected: {reprStr error}")
          let insert := SourceCoreMappingWithDefault.insert layout comparison.expression (.var 0) (.var 1) (.var 2)
          assertTrue (infer? [SourceCoreMappingWithDefault.type layout, layout.keyType, layout.valueType] insert context.checked.catalog.definitions == some (LanguageResult.resultType (SourceCoreMappingWithDefault.type layout))) "mapping insertion checker failed"
          let (inserted, insertStore) ← completed insert [encodedMapping.value, encodedKey.value, encodedReplacement.value] before
          assertTrue (insertStore.length == before.length + context.checked.catalog.entries.length + 1) "mapping insertion administrative count changed"
          match inserted with
          | .inRight .word value => decoded encodedReplacement.context (.mapping sourceKey sourceValue) value expectedInserted
          | _ => throw (IO.userError "standalone insertion unexpectedly applied missing-default guard")
          let keyId : ExpressionId := ⟨⟨owner, 7⟩⟩
          let route : SourceCoreCompatibleDataPlaces.Route := ⟨.mapping sourceKey sourceValue,
            SourceCoreMappingWithDefault.type layout, layout.valueType, [.index layout keyId sourceValue], none⟩
          let prepared ← match SourceCoreCompatibleDataPlaces.prepare context 200 route (word 900) (fun _ => missing) with
            | .ok prepared => pure prepared
            | .error error => throw (IO.userError s!"compatible place preparation failed: {reprStr error}")
          let getter := SourceCoreCompatibleDataPlaces.getter prepared layout.keyType
          let setter := SourceCoreCompatibleDataPlaces.setter prepared layout.keyType
          assertTrue (infer? [] getter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) layout.keyType) (LanguageResult.resultType prepared.optionalLeaf))) "generated getter checker failed"
          assertTrue (infer? [] setter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product layout.keyType layout.valueType)) (LanguageResult.resultType route.rootType))) "generated setter checker failed"
          let (read, readStore) ← completed (.apply getter (.var 0)) [.pair (.inRight .unit encodedMapping.value) encodedKey.value] before
          assertTrue (readStore.length == before.length + context.checked.catalog.entries.length + 1) "getter allocation count changed"
          match expectedRead, read with
          | some expected, .inRight .word (.inRight .unit value) => decoded encodedReplacement.context sourceValue value expected
          | none, .inLeft _ (.word token) => assertTrue (token == missing.add header) "getter changed missing-default token"
          | _, _ => throw (IO.userError "generated getter result differs from lookup")
          let (updated, updateStore) ← completed (.apply setter (.var 0))
            [.pair (.inRight .unit encodedMapping.value) (.pair encodedKey.value encodedReplacement.value)] before
          match expectedRead, updated with
          | some _, .inRight .word value =>
            decoded encodedReplacement.context (.mapping sourceKey sourceValue) value expectedInserted
            assertTrue (updateStore.length == before.length + 2 * (context.checked.catalog.entries.length + 1)) "setter did not select before insert"
          | none, .inLeft _ (.word token) =>
            assertTrue (token == missing.add header) "setter missing-default token changed"
            assertTrue (updateStore.length == before.length + context.checked.catalog.entries.length + 1) "setter inserted after missing default"
          | _, _ => throw (IO.userError "setter guard/result mismatch")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"mapping fixture failed: {reprStr error}")
  let box ← match program.signatures.dataTypes.filter (·.name == "Box") with
    | [signature] => pure signature | _ => throw (IO.userError "mapping Box signature missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mapping Box constructor missing")
  let boxType : TypeSystem.Ty := .nominal box.id []
  let item : DataConstructorInstantiation := ⟨constructor.id, [], [.word], boxType⟩
  let proxy : TypeSystem.Ty := .proxy .word
  let rawProxy : TypeSystem.Ty := .proxy (.comptime .word)
  let table : TypeSystem.Ty := .mapping .word rawProxy
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 300
      [.mapping .word proxy, .mapping proxy .word, .mapping .word boxType, .mapping .word table] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"mapping catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let duplicates : SourceCoreDataValues.Value := .mapping .word rawProxy [(.word (word 1), .proxy (.comptime .word)), (.word (word 1), .proxy .word)]
  let sources : List (Dynamic.Value × Dynamic.Value) := [(.word (word 1), .proxy (.comptime .word)), (.word (word 1), .proxy .word)]
  have duplicatesMeaning : CompatibleEncoding.Means duplicates (.mapping .word rawProxy sources) := .mapping (.prepend (.word _) (.proxy _) (.prepend (.word _) (.proxy _) .empty))
  exercise context box.id .word rawProxy duplicates (.word (word 1)) (.proxy .word) sources (.word (word 1)) duplicatesMeaning (.word _)
    (some (.proxy (.comptime .word))) (.mapping .word rawProxy [(.word (word 1), .proxy .word), (.word (word 1), .proxy .word)])
  exercise context box.id .word rawProxy duplicates (.word (word 2)) (.proxy .word) sources (.word (word 2)) duplicatesMeaning (.word _)
    (some (.proxy (.comptime .word))) (.mapping .word rawProxy ([(.word (word 1), .proxy (.comptime .word)), (.word (word 1), .proxy .word), (.word (word 2), .proxy .word)]))
  exercise context box.id proxy .word (.mapping proxy .word [(.proxy .word, .word (word 3)), (.proxy (.comptime .word), .word (word 4))])
    (.proxy (.comptime .word)) (.word (word 8)) [(.proxy .word, .word (word 3)), (.proxy (.comptime .word), .word (word 4))] (.proxy (.comptime .word))
    (.mapping (.prepend (.proxy _) (.word _) (.prepend (.proxy _) (.word _) .empty))) (.proxy _)
    (some (.word (word 4))) (.mapping proxy .word [(.proxy .word, .word (word 3)), (.proxy (.comptime .word), .word (word 8))])
  exercise context box.id .word boxType (.mapping .word boxType []) (.word (word 1)) (.constructed item [.word (word 7)]) [] (.word (word 1))
    (.mapping .empty) (.word _) none (.mapping .word boxType [(.word (word 1), .constructed item [.word (word 7)])])
  exercise context box.id .word table (.mapping .word table []) (.word (word 1)) (.mapping .word rawProxy []) [] (.word (word 1))
    (.mapping .empty) (.word _) (some (.mapping .word rawProxy [])) (.mapping .word table [(.word (word 1), .mapping .word rawProxy [])])
  IO.println "compatible mapping lookup/default/fault/ordered update proofs GREEN"

end Tests.SourceCoreCompatibleMappingProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMappingVirtualRoot
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Real checked assignment metadata reaches describe's literal generator.
The root stays absent while virtual defaults and generated helpers execute. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMappingVirtualRoot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.VirtualRoot

private def w (value : Nat) : Word := Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "function scalar() returns (Word) { let table: mapping(Word => Word); table[1] = 7; return 0; }",
    "function nested() returns (Word) { let table: mapping(Word => mapping(Word => @Word)); let other: mapping(Word => @Word); table[1] = other; return 0; }",
    "function missing() returns (Word) { let table: mapping(Word => Box); table[1] = .Item(7); return 0; }"
  ]}] }
private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "virtual-root function missing")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => match plan.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "virtual-root specialization count changed")
  | other => throw (IO.userError s!"virtual-root specialization failed: {reprStr other}")
private def assignmentFor (source : TypedSource) : IO (StatementNode × AssignmentResolution) :=
  match source.nodes.filterMap (fun
    | .statement node => match node.form with | .assignValue assignment _ _ => some (node, assignment) | _ => none
    | _ => none) with
  | [assignment] => pure assignment
  | _ => throw (IO.userError "virtual-root assignment count changed")
private def encode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : SourceCoreDataValues.Value) :
    IO (SourceCoreCompatibleValues.Encoded 500 context type value) :=
  match SourceCoreCompatibleValues.encode 500 context type value with
  | .ok encoded => pure encoded | .error error => throw (IO.userError s!"virtual-root encode failed: {reprStr error}")
private def decode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : Value) (expected : SourceCoreDataValues.Value) : IO Unit :=
  match SourceCoreCompatibleValues.decode 500 context type value with
  | .ok decoded => assertTrue (decoded == expected) "virtual-root raw/default value changed"
  | .error error => throw (IO.userError s!"virtual-root decode failed: {reprStr error}")
private def completed (code : Expr) (environment : Environment) (before : Store) : IO (Value × Store) := do
  let result ← match runStateful 200000 (.initial code environment before) with
    | .done value store => pure (value, store)
    | other => throw (IO.userError s!"virtual-root run failed: {reprStr other}")
  assertTrue (result.2.take before.length == before) "virtual-root materialized the absent source cell"
  match runStateful 1 (.initial code environment before) with
  | .outOfFuel checkpoint =>
    match runStateful 200000 checkpoint with
    | .done value store => assertTrue (value == result.1 && store == result.2) "virtual-root resume changed result"
    | _ => throw (IO.userError "virtual-root resume failed")
  | _ => throw (IO.userError "virtual-root fixture omitted checkpoint")
  pure result

private def exercise (initial : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (expectedRead : Option SourceCoreDataValues.Value) (replacement : SourceCoreDataValues.Value) : IO Unit := do
  let (node, assignment) ← assignmentFor source
  match binding : SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root with
  | .error error => throw (IO.userError s!"virtual-root binder failed: {reprStr error}")
  | .ok binder =>
    match declared : binder.scheme.body with
    | .mapping key value =>
      let empty ← encode initial (.mapping key value) (.mapping key value [])
      let context := empty.context
      match described : SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source (.occurrence node.id.occurrence) assignment with
      | .error error => throw (IO.userError s!"virtual-root describe failed: {reprStr error}")
      | .ok route =>
        have receipt := generated_of_describe binding declared described
        let absent := Value.inLeft route.rootType .unit
        let before := [absent, Value.integer (-123)]
        let prepared ← match SourceCoreCompatibleDataPlaces.prepare context 200 route (w 900) (fun _ => w 1000) with
          | .ok prepared => pure prepared | .error error => throw (IO.userError s!"virtual-root prepare failed: {reprStr error}")
        -- The proof consumer takes the actual describe equation; no literal
        -- evaluation or alternative default implementation is supplied.
        have _normalizes := generated_normalizes (prepared := ⟨route, [], [], w 900⟩) receipt
          (noFunctions context.checked.catalog) [] [] [absent] before (.var 0) (.var rfl)
        let normalization := SourceCoreCompatibleDataPlaces.normalizeRoot prepared (.var 0)
        assertTrue (infer? [OptionalCell.cellType route.rootType] normalization context.checked.catalog.definitions == some (OptionalCell.cellType route.rootType)) "virtual-root normalization checker failed"
        let (normalized, sameStore) ← completed normalization [absent] before
        assertTrue (sameStore == before) "normalization allocated or wrote a cell"
        match normalized with
        | .inRight .unit raw => decode context (.mapping key value) raw (.mapping key value [])
        | _ => throw (IO.userError "normalization left mapping absent")
        let header ← match empty.value with
          | .pair (.word header) _ => pure header | _ => throw (IO.userError "virtual-root raw header missing")
        assertTrue (context.registry.lookup header == some (.mapping key value)) "virtual-root header metadata changed"
        let replacementSource := replacement
        let replacement ← encode context value replacement
        let getter := SourceCoreCompatibleDataPlaces.getter prepared .word
        let setter := SourceCoreCompatibleDataPlaces.setter prepared .word
        assertTrue (infer? [] getter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) .word) (LanguageResult.resultType prepared.optionalLeaf))) "virtual-root getter checker failed"
        assertTrue (infer? [] setter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product .word route.leafType)) (LanguageResult.resultType route.rootType))) "virtual-root setter checker failed"
        let (read, readStore) ← completed (.apply getter (.var 0)) [.pair absent (.word (w 1))] before
        assertTrue (readStore.length == before.length + context.checked.catalog.entries.length + 1) "virtual-root getter administrative count changed"
        match expectedRead, read with
        | some expected, .inRight .word (.inRight .unit selected) => decode context value selected expected
        | none, .inLeft _ (.word token) => assertTrue (token == (w 1000).add header) "virtual-root missing-default token changed"
        | _, _ => throw (IO.userError "virtual-root getter result mismatch")
        let (updated, updateStore) ← completed (.apply setter (.var 0)) [.pair absent (.pair (.word (w 1)) replacement.value)] before
        match expectedRead, updated with
        | some _, .inRight .word raw =>
          match SourceCoreCompatibleValues.decode 500 replacement.context (.mapping key value) raw with
          | .ok (.mapping actualKey actualValue entries) =>
            assertTrue (actualKey == key && actualValue == value && entries == [(.word (w 1), replacementSource)]) "virtual-root setter changed raw metadata or replacement"
          | _ => throw (IO.userError "virtual-root setter carrier invalid")
          assertTrue (updateStore.length == before.length + 2 * (context.checked.catalog.entries.length + 1)) "virtual-root setter administrative count changed"
        | none, .inLeft _ (.word token) =>
          assertTrue (token == (w 1000).add header) "virtual-root setter missing-default token changed"
          assertTrue (updateStore.length == before.length + context.checked.catalog.entries.length + 1) "virtual-root setter inserted after missing-default"
        | _, _ => throw (IO.userError "virtual-root setter result mismatch")
    | _ => throw (IO.userError "virtual-root fixture binder stopped being bare mapping")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"virtual-root source rejected: {reprStr error}")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "virtual-root Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "virtual-root constructor missing")
  let boxType := TypeSystem.Ty.nominal box.id []
  let item : DataConstructorInstantiation := ⟨constructor.id, [], [.word], boxType⟩
  let nested := TypeSystem.Ty.mapping .word (.proxy .word)
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 300 [.mapping .word .word, .mapping .word nested, .mapping .word boxType] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"virtual-root catalog rejected: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  exercise context (← sourceFor program "scalar") (some (.word Word.zero)) (.word (w 7))
  exercise context (← sourceFor program "nested") (some (.mapping .word (.proxy .word) [])) (.mapping .word (.proxy .word) [])
  exercise context (← sourceFor program "missing") none (.constructed item [.word (w 7)])
  IO.println "compatible mapping virtual-root proofs GREEN"

end Tests.SourceCoreCompatibleMappingVirtualRoot
end
