import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityEncoding
import Solcore.Frontend.ProgramChecking

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
