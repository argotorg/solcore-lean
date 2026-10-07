import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport

/-! The original owned function relation is retained as one constructor.
A separate method-lambda constructor stores its authentic Header-free body
support, full Source seed, captures and immutable key. Forgetting only these
extra receipts reaches the existing low indexed function model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedMethodLambdaSupport (Support SourceOrigin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}

/-- Method support is an explicit alternative to the unchanged original
Header-ranked support. Every lambda still retains full static body receipts. -/
inductive Represents (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {sourceType source native type}
      (related : CallableIndexedOwnedFunctionValues.Represents headers keys registry faults mapping world sourceType source native type) :
      Represents headers keys registry faults mapping world sourceType source native type
  | method_lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment} {callerPrefix : Nat}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code registry faults) (origin : SourceOrigin body history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

theorem Represents.forget {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases related with
  | prior original => exact original.forget
  | method_lambda owner captured code history body origin globals referenceIndex typed =>
    exact .lambda captured code history typed

def model (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => Represents headers keys bodyRegistry faults mapping world
  projection := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).projection
    (registry := bodyRegistry) related.forget
  runtime_hasType := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) related.forget
  source_function := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).source_function
    (registry := bodyRegistry) related.forget
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | prior original => exact .prior ((CallableIndexedOwnedFunctionValues.model headers keys bodyRegistry faults profile).extend
        original registries maps worlds)
    | method_lambda owner captured code history body origin globals referenceIndex typed =>
      exact .method_lambda owner (captured.extend maps worlds) code history body origin globals referenceIndex (typed.weaken worlds)

theorem observations (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry) related.forget

theorem runtime_views (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry) related.forget

/-- The complete original owned relation embeds without altering its payload. -/
theorem includes_original (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedFunctionValues.model headers keys bodyRegistry faults profile).Includes
      (model headers keys bodyRegistry faults profile) := fun related => .prior related

/-- Explicit domain embeddings retain the full immutable method-lambda key. -/
theorem Represents.map_keys {keys futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    Represents headers futureKeys registry faults mapping world sourceType source native type := by
  cases related with
  | prior original => exact .prior (original.map_keys embedding)
  | @method_lambda function scope actual callerPrefix owner captured code history body origin globals referenceIndex typed =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations callerPrefix scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .method_lambda (embedding.map owner) captured code history body origin actualGlobals referenceIndex typed

theorem includes {keys futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (model headers keys bodyRegistry faults profile).Includes (model headers futureKeys bodyRegistry faults profile) :=
  fun related => related.map_keys embedding

/-- The new constructor supplies the complete same-Code method receipt.
Existing closures retain their original complete owned representation. -/
theorem Represents.closure_cases {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type) :
    CallableIndexedOwnedFunctionValues.Represents headers keys registry faults mapping world sourceType (.closure function) native type ∨
    ∃ owner : OwnedKey keys, ∃ scope actual callerPrefix,
      ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
        (code : Code compiled.indexed function scope captured.administrative) (history : History code)
        (body : Support code registry faults),
        SourceOrigin body history ∧
        CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation ∧
        code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length ∧
        sourceType = FunctionValues.sourceType function ∧ native = value code captured.embedding history.native actual ∧
        type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore ∧
        RuntimeValueHasType world (value code captured.embedding history.native actual)
          (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions := by
  cases related with
  | prior original => exact Or.inl original
  | method_lambda owner captured code history body origin globals referenceIndex typed =>
    exact Or.inr ⟨owner, _, _, _, captured, code, history, body, origin, globals, referenceIndex, rfl, rfl, rfl, typed⟩

/-- Genuine method-site formation reads the existing physical frame and
retains its actual full owned row. The original primitive producers establish
Source formation, emitted completion and native typing internally. -/
theorem method_lambda_of_formation
    {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment} {callerPrefix : Nat}
    (pool : CallableIndexedAuthorityPool.Pool (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys mapping world heap store)
    (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (code : Code compiled.indexed function scope captured.administrative) (history : History code)
    (body : Support code bodyRegistry faults) (origin : SourceOrigin body history)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (current : (pool.rows owner.position).authority.current = history.native)
    (ghost : (pool.rows owner.position).authority.ghost = history.ghost)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store ∧
    Represents headers keys bodyRegistry faults mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding history.native actual) ∧ finalStore = store) := by
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [referenceIndex]
    exact globals.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (pool.rows owner.position).authority.frame.read
    rw [(pool.rows owner.position).frame_eq, current] at actualRead
    exact actualRead
  have sameHistory : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      history.native history.ghost := by
    simpa only [current, ghost] using (pool.rows owner.position).authority.frame.history
  have sourceTrace := source_formation code (Program.ofChecked compiled.sourceProgram) heap ordinary coercions
  have nativeTrace := formation_evaluates captured code history reference read
  have related := formation_represents captured code history stored reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) related
  exact ⟨sourceTrace, nativeTrace, .method_lambda owner captured code history body origin globals referenceIndex typed,
    fun _ _ completed => Core.evaluation_deterministic completed nativeTrace⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaValues
