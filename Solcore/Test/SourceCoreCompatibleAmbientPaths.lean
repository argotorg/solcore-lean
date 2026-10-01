import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientEncoding
import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedRuns
import Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked source supplies roots and index occurrences. The retained ordinal
member path is assembled explicitly (source member syntax is not asserted).
The actual indexed compiler supplies the ambient frame/marker suffix.
Actual describe/prepare/checker/run preserve raw constructor IDs, raw mapping
headers, siblings, nested defaults, and ordered duplicate entries. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientPaths
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths

private def w (n : Nat) : Word := Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "function probe(seed: Word) returns (Word) { let f = lam(item: Word) { return item; }; return f(seed); }",
    "enum Holder<T> { Wrap(mapping(Word => T), Word), Other(mapping(Word => T), Word) }",
    "function mixed(root: mapping(Word => Holder<Word>), value: Holder<Word>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function missing(root: mapping(Word => Holder<Box>), value: Holder<Box>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function nested(root: mapping(Word => mapping(Word => @Word)), value: mapping(Word => @Word), key: Word) returns (Word) { root[key] = value; return 0; }"
  ]}] }
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

/-- Actual encoded virtual roots transport to the full indexed definition
suffix. Normalization keeps the absent source cell and the entire native store;
its child value/default is derived from the real encoder receipt. -/
theorem virtual_root_under_indexed {context : SourceCoreCompatibleValues.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared context.checked)
    (functions : FunctionModel context.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions artifact))
    {prepared : SourceCoreCompatibleDataPlaces.Prepared} {key valueType : TypeSystem.Ty}
    (generated : VirtualRoot.Generated context prepared.route key valueType)
    (store : Store) (mapping : GeneralHeap.LocationMap) (world : StoreTyping) :
    ∃ header layout fallback,
      CompatiblePayload.ValueRep context.checked context.registry functions mapping world (.mapping key valueType)
        (.mapping key valueType []) (Transport.carrier header fallback layout []) (SourceCoreMappingWithDefault.type layout) ∧
      Dynamic.RootInitialValue ⟨.mapping key valueType, none, none⟩ (some (.mapping key valueType [])) ∧
      Evaluates [.inLeft prepared.route.rootType .unit] store
        (SourceCoreCompatibleDataPlaces.normalizeRoot prepared (.var 0))
        (.inRight .unit (Transport.carrier header fallback layout [])) store := by
  obtain ⟨header, layout, fallback, fields, root⟩ := generated_root generated functions mapping world (.refl _)
  exact ⟨header, layout, fallback, fields.represents, root.initial, root.normalize _ store (.var 0) (.var rfl)⟩

/-- A static mixed-path tree and the actual indexed ambient receipt suffice
for whole generated getter meaning and reflection. Runtime child evaluations
are outputs of the structural theorem, not premises in this consumer. -/
theorem mixed_read_under_indexed {checked : SourceCoreCompatibleCatalog.Checked}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : SourceCoreCompatibleDataPlaces.Prepared} {keys : List Value}
    {leafType sourceType : TypeSystem.Ty} {leafCore : Ty}
    {cell : Dynamic.Cell} {source leaf : Dynamic.Value} {optional value : Value}
    {steps : List SourceCoreCompatibleDataPlaces.PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (root : RootInput prepared cell optional source value)
    (tree : ReadTree checked registry functions mapping world prepared keys leafType leafCore sourceType source value steps projections leaf count)
    (stepsEqual : prepared.steps = steps) (nonempty : steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr)
    (selected : DataEquality.Selects environment argument (.pair optional (DataPatternValues.packValues keys))) :
    ∃ native after administrative,
      Dynamic.RootInitialValue cell (some source) ∧ Dynamic.ProjectionsRead (some source) projections (some leaf) ∧
      ValueRep checked registry functions mapping world leafType leaf native leafCore ∧
      FiniteRun environment store (.apply (SourceCoreCompatibleDataPlaces.getter prepared keyType) argument)
        (.inRight .word (.inRight .unit native)) after ∧
      after = store ++ administrative ∧ administrative.length = count :=
  getter_preserves_run root tree stepsEqual nonempty faithful functionLeaves keyLength environment store keyType argument selected

private def exercise (initial : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions initial.checked.catalog.definitions) (inertStore : Store) (source : TypedSource)
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
  let before := inertStore ++ [optional, Value.integer (-99)]
  let getter := SourceCoreCompatibleDataPlaces.getter prepared keyType
  let setter := SourceCoreCompatibleDataPlaces.setter prepared keyType
  assertTrue (infer? [] getter ambient.definitions == some (.function (.product (OptionalCell.cellType route.rootType) keyType) (LanguageResult.resultType prepared.optionalLeaf))) "mixed getter checker failed"
  assertTrue (infer? [] setter ambient.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product keyType route.leafType)) (LanguageResult.resultType route.rootType))) "mixed setter checker failed"
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
  let requests := program.signatures.functions.map (fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"ambient mixed worklist: {reprStr other}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"ambient mixed base: {reprStr error}")
  let artifact ← match SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"ambient mixed indexed compiler: {reprStr error}")
  let probe ← match program.signatures.functions.find? (·.name == "probe") with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey)
    | none => throw (IO.userError "ambient mixed probe missing")
  let completion ← match artifact.runSource probe [.word (w 7)] 100000 500 with
    | .ok completed => pure completed
    | .error error => throw (IO.userError s!"ambient mixed probe run: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w 7) "ambient mixed probe changed its result"
  | other => throw (IO.userError s!"ambient mixed probe did not complete: {reprStr other}")
  let before := SourceCoreCallableIndexedLedger.store completion
  let full := CallableIndexedAmbient.ambientDefinitions artifact
  have _prefix := CallableIndexedAmbient.definitions_exact artifact
  assertTrue (!artifact.layouts.entries.isEmpty) "ambient mixed actual source marker suffix missing"
  let context := SourceCoreCompatibleValues.Context.initial automatic.checked
  let metadata : DataConstructorInstantiation := ⟨constructor.id, [(parameter, .comptime .word)], [.mapping .word (.comptime .word), .word], rawHolder⟩
  let inner : SourceCoreDataValues.Value := .mapping .word (.comptime .word) [(.word (w 1), .word (w 2)), (.word (w 1), .word (w 9))]
  let held := SourceCoreDataValues.Value.constructed metadata [inner, .word (w 55)]
  let root := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), held), (.word (w 1), held)]
  let updatedInner := SourceCoreDataValues.Value.mapping .word (.comptime .word) [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  let updated := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), .constructed metadata [updatedInner, .word (w 55)]), (.word (w 1), held)]
  exercise context full before (← sourceFor program "mixed") (.mapping .word holderWord) .word root (.word (w 7)) true false (some (.word (w 2))) (some updated)
  let boxType := TypeSystem.Ty.nominal box.id []
  let item : DataConstructorInstantiation := ⟨boxCtor.id, [], [.word], boxType⟩
  let boxHolder : DataConstructorInstantiation := ⟨constructor.id, [(parameter, boxType)], [.mapping .word boxType, .word], holderBox⟩
  let emptyInner := SourceCoreDataValues.Value.mapping .word boxType []
  let innerEncoded ← encode context (.mapping .word boxType) emptyInner
  let header ← match innerEncoded.value with
    | .pair (.word header) _ => pure header | _ => throw (IO.userError "mixed inner raw header absent")
  let missingRoot := SourceCoreDataValues.Value.mapping .word holderBox [(.word (w 1), .constructed boxHolder [emptyInner, .word (w 55)])]
  exercise innerEncoded.context full before (← sourceFor program "missing") (.mapping .word holderBox) boxType missingRoot (.constructed item [.word (w 7)]) true false none none (some header)
  let empty := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word)) []
  let updated := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word))
    [(.word (w 1), .mapping .word (.proxy .word) [(.word (w 1), .proxy .word)])]
  exercise context full before (← sourceFor program "nested") nested (.proxy .word) empty (.proxy .word) false true (some (.proxy .word)) (some updated)
  IO.println "compatible ambient mixed member/mapping paths proofs GREEN"

end Tests.SourceCoreCompatibleAmbientPaths
