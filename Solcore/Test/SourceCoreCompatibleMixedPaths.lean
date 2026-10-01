import Solcore.SourceSemantics.CoreLowering.CompatibleMemberCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedRuns
import Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked source supplies roots and index occurrences. The retained ordinal
member path is assembled explicitly (source member syntax is not asserted).
Actual describe/prepare/checker/run preserve raw constructor IDs, raw mapping
headers, siblings, nested defaults, and ordered duplicate entries. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMixedPaths
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths

private def w (n : Nat) : Word := Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "enum Holder<T> { Wrap(mapping(Word => T), Word), Other(mapping(Word => T), Word) }",
    "function mixed(root: mapping(Word => Holder<Word>), value: Holder<Word>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function missing(root: mapping(Word => Holder<Box>), value: Holder<Box>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function nested(root: mapping(Word => mapping(Word => @Word)), value: mapping(Word => @Word), key: Word) returns (Word) { root[key] = value; return 0; }"
  ]}] }
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

private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "mixed function missing")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => match plan.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "mixed specialization count changed")
  | other => throw (IO.userError s!"mixed specialization failed: {reprStr other}")
private def assignmentFor (source : TypedSource) : IO (StatementNode × AssignmentResolution × ExpressionId) := do
  let (node, assignment) ← match source.nodes.filterMap (fun
    | .statement node => match node.form with | .assignValue assignment _ _ => some (node, assignment) | _ => none
    | _ => none) with
    | [assignment] => pure assignment | _ => throw (IO.userError "mixed assignment missing")
  match assignment.target.projections with
  | [.index key] => pure (node, assignment, key)
  | _ => throw (IO.userError "mixed original assignment path changed")
private def encode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : SourceCoreDataValues.Value) :
    IO (SourceCoreCompatibleValues.Encoded 500 context type value) :=
  match SourceCoreCompatibleValues.encode 500 context type value with
  | .ok encoded => pure encoded | .error error => throw (IO.userError s!"mixed encode failed: {reprStr error}")
private def decode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (native : Value) (expected : SourceCoreDataValues.Value) : IO Unit :=
  match SourceCoreCompatibleValues.decode 500 context type native with
  | .ok actual => assertTrue (actual == expected) "mixed path lost raw metadata, sibling, or ordered duplicate"
  | .error error => throw (IO.userError s!"mixed decode failed: {reprStr error}")
private def completed (code : Expr) (environment : Environment) (before : Store) : IO (Value × Store) := do
  let result ← match runStateful 500000 (.initial code environment before) with
    | .done value after => pure (value, after)
    | other => throw (IO.userError s!"mixed helper failed: {reprStr other}")
  assertTrue (result.2.take before.length == before) "mixed helper changed source store prefix"
  match runStateful 7 (.initial code environment before) with
  | .outOfFuel checkpoint =>
    match runStateful 500000 checkpoint with
    | .done value after => assertTrue (value == result.1 && after == result.2) "mixed resume changed value/store"
    | _ => throw (IO.userError "mixed resume failed")
  | _ => throw (IO.userError "mixed fixture no longer checkpoints")
  pure result

/-- This consumer starts with actual memberStep and public encoding receipts.
Every projected child retains its full independent payload relation, including
nested mapping defaults and raw aliases; no helper execution is a premise. -/
private theorem member_receipt {context : SourceCoreCompatibleValues.Context}
    {root : TypeSystem.Ty} {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {step : SourceCoreCompatibleDataPlaces.Step} {field : TypeSystem.Ty}
    {metadata : DataConstructorInstantiation} {payload : List SourceCoreDataValues.Value}
    {sourcePayload : List Dynamic.Value}
    {encoded : SourceCoreCompatibleValues.Encoded 500 context root (.constructed metadata payload)}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
    (selected : context.checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (accepted : SourceCoreCompatibleDataPlaces.memberStep context.checked context.checked.signatures site binder root 0 = .ok (step, field))
    (encodedAccepted : SourceCoreCompatibleValues.encode 500 context root (.constructed metadata payload) = .ok encoded)
    (meaning : CompatibleEncoding.Meanings payload sourcePayload) :
    ∃ identity branches nativeField,
      step = .member identity 0 branches nativeField ∧
      ∃ sourceChild valueChild actual,
        Dynamic.ValueAt sourcePayload 0 sourceChild ∧
        SourceCoreRawMetadata.runtimeType actual = SourceCoreRawMetadata.runtimeType field ∧
        CompatiblePayload.ValueRep context.checked encoded.context.registry (noFunctions context.checked.catalog) [] [] actual sourceChild valueChild nativeField := by
  obtain ⟨identity, branches, nativeField, stepEq, certificate⟩ :=
    CompatibleMemberCertificates.certificate_of_memberStep nominal selected accepted
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions context.checked.catalog)
    encodedAccepted (.constructed meaning) [] []
  obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
  obtain ⟨_, branch, actual, sourceChild, valueChild, _, _, _, _, view, _, sourceAt, _, related⟩ :=
    certificate.select nominal selected fields
  exact ⟨identity, branches, nativeField, stepEq, sourceChild, valueChild, actual, sourceAt, view, related⟩

private def exercise (initial : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (rootType leafType : TypeSystem.Ty) (rootCarrier replacement : SourceCoreDataValues.Value)
    (member : Bool) (optionalAbsent : Bool) (expectedRead : Option SourceCoreDataValues.Value)
    (expectedUpdate : Option SourceCoreDataValues.Value) (missingHeader : Option Word := none) : IO Unit := do
  let (node, assignment, key) ← assignmentFor source
  let assignment := { assignment with target := { assignment.target with
    type := leafType
    projections := if member then [.index key, .member "entries" 0, .index key] else [.index key, .index key]}}
  let root ← encode initial rootType rootCarrier
  let replacement ← encode root.context leafType replacement
  let context := replacement.context
  let route ← match SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source (.occurrence node.id.occurrence) assignment with
    | .ok route => pure route | .error error => throw (IO.userError s!"mixed describe failed: {reprStr error}")
  let prepared ← match preparedAccepted : SourceCoreCompatibleDataPlaces.prepare context 200 route (w 900) (fun _ => w 1000) with
    | .ok prepared =>
      have _receipt := CompatibleMixedPreparation.of_prepare preparedAccepted
      pure prepared | .error error => throw (IO.userError s!"mixed prepare failed: {reprStr error}")
  assertTrue (prepared.keys.map Prod.fst == [key, key]) "mixed key occurrences/positions changed"
  let keys := Value.pair (.word (w 1)) (.word (w 1))
  let keyType := Ty.product .word .word
  let optional := if optionalAbsent then Value.inLeft route.rootType .unit else .inRight .unit root.value
  let before := [optional, Value.integer (-99)]
  let getter := SourceCoreCompatibleDataPlaces.getter prepared keyType
  let setter := SourceCoreCompatibleDataPlaces.setter prepared keyType
  assertTrue (infer? [] getter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) keyType) (LanguageResult.resultType prepared.optionalLeaf))) "mixed getter checker failed"
  assertTrue (infer? [] setter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product keyType route.leafType)) (LanguageResult.resultType route.rootType))) "mixed setter checker failed"
  let (read, readStore) ← completed (.apply getter (.var 0)) [.pair optional keys] before
  assertTrue (readStore.length == before.length + 2 * (context.checked.catalog.entries.length + 1)) "mixed lookup allocation count changed"
  match expectedRead, read with
  | some expected, .inRight .word (.inRight .unit value) => decode context leafType value expected
  | none, .inLeft _ (.word token) => assertTrue (some token == missingHeader.map ((w 1000).add)) "mixed fault used outer raw header"
  | _, _ => throw (IO.userError s!"mixed getter outcome changed: {reprStr read}")
  let (updated, updateStore) ← completed (.apply setter (.var 0)) [.pair optional (.pair keys replacement.value)] before
  match expectedUpdate, updated with
  | some expected, .inRight .word value =>
    decode context rootType value expected
    assertTrue (updateStore.length == before.length + 4 * (context.checked.catalog.entries.length + 1)) "mixed setter skipped selection or outer insertion"
  | none, .inLeft _ (.word token) =>
    assertTrue (some token == missingHeader.map ((w 1000).add)) "mixed setter fault token changed"
    assertTrue (updateStore.length == readStore.length) "mixed setter inserted after inner failure"
  | _, _ => throw (IO.userError s!"mixed setter outcome changed: {reprStr updated}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"mixed source rejected: {reprStr error}")
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "mixed Holder missing")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mixed Wrap missing")
  let parameter ← match holder.parameters with
    | [parameter] => pure parameter | _ => throw (IO.userError "mixed Holder parameter changed")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "mixed Box missing")
  let boxCtor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mixed Item missing")
  let holderWord := TypeSystem.Ty.nominal holder.id [.word]
  let rawHolder := TypeSystem.Ty.nominal holder.id [.comptime .word]
  let holderBox := TypeSystem.Ty.nominal holder.id [.nominal box.id []]
  let nested := TypeSystem.Ty.mapping .word (.mapping .word (.proxy .word))
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 500 [.mapping .word holderWord, .mapping .word holderBox, nested] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"mixed catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let metadata : DataConstructorInstantiation := ⟨constructor.id, [(parameter, .comptime .word)], [.mapping .word (.comptime .word), .word], rawHolder⟩
  let inner : SourceCoreDataValues.Value := .mapping .word (.comptime .word) [(.word (w 1), .word (w 2)), (.word (w 1), .word (w 9))]
  let held := SourceCoreDataValues.Value.constructed metadata [inner, .word (w 55)]
  let root := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), held), (.word (w 1), held)]
  let updatedInner := SourceCoreDataValues.Value.mapping .word (.comptime .word) [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  let updated := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), .constructed metadata [updatedInner, .word (w 55)]), (.word (w 1), held)]
  exercise context (← sourceFor program "mixed") (.mapping .word holderWord) .word root (.word (w 7)) true false (some (.word (w 2))) (some updated)
  let boxType := TypeSystem.Ty.nominal box.id []
  let item : DataConstructorInstantiation := ⟨boxCtor.id, [], [.word], boxType⟩
  let boxHolder : DataConstructorInstantiation := ⟨constructor.id, [(parameter, boxType)], [.mapping .word boxType, .word], holderBox⟩
  let emptyInner := SourceCoreDataValues.Value.mapping .word boxType []
  let innerEncoded ← encode context (.mapping .word boxType) emptyInner
  let header ← match innerEncoded.value with
    | .pair (.word header) _ => pure header | _ => throw (IO.userError "mixed inner raw header absent")
  let missingRoot := SourceCoreDataValues.Value.mapping .word holderBox [(.word (w 1), .constructed boxHolder [emptyInner, .word (w 55)])]
  exercise innerEncoded.context (← sourceFor program "missing") (.mapping .word holderBox) boxType missingRoot (.constructed item [.word (w 7)]) true false none none (some header)
  let empty := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word)) []
  let updated := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word))
    [(.word (w 1), .mapping .word (.proxy .word) [(.word (w 1), .proxy .word)])]
  exercise context (← sourceFor program "nested") nested (.proxy .word) empty (.proxy .word) false true (some (.proxy .word)) (some updated)
  IO.println "compatible mixed member/mapping paths proofs GREEN"

end Tests.SourceCoreCompatibleMixedPaths
