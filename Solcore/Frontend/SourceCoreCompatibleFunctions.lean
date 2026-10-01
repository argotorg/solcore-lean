import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.Frontend.SourceCorePlanCatalog
import Solcore.Frontend.SourceCoreCompatibleDataMatches
import Solcore.Frontend.SourceCoreCompatibleInputs

/-! Cached source-compatible functions reuse the contextual compiler and
native runner. Original contracts and local-evidence receipts own the inventory;
data inputs extend only the raw metadata registry. Dynamic missing-default
diagnostics use disjoint reserved ranges before callable tokens are assigned.

This artifact supplies native typed execution and a data codec. Legacy source
heap export and global/builtin/function value adapters are separate boundaries.
It does not evaluate source expressions or change checker admission. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleFunctions
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev DataValue := SourceCoreCompatibleValues.Value
abbrev Values := SourceCoreCompatibleValues.Context
abbrev Native := SourceCoreGeneralEntry.NativeEntry
abbrev NativeResult := SourceCoreGeneralEntry.Result

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | locals (error : SourceCoreLocalPolymorphism.Error)
  | contexts (error : SourceCoreStageCodebook.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  | callables (error : SourceCoreCallableFaultSites.Error)
  | native (error : SourceCoreGeneralEntry.NativeCompileError)
  | missingRoot (key : Key)
  | inputs (error : SourceCoreCompatibleInputs.Error)
  deriving Repr

structure Entry (checked : Checked) where private mk ::
  key : Key
  inputs : List TypedBinder
  sourceResultType : TypeSystem.Ty
  native : Native checked.catalog.definitions

structure SourceInputs (checked : Checked) where private mk ::
  context : SourceCoreCompatibleInputs.Context
  valuesExact : context.values = SourceCoreCompatibleValues.Context.initial checked

private def prepareSourceInputs (checked : Checked) (plan validationPlan : Plan)
    (globals : List SourceCoreCalls.Signature)
    (native : Option SourceCoreGeneralFunctions.CallableContext) : Except Error (SourceInputs checked) :=
  match accepted : SourceCoreCompatibleInputs.prepare
      (SourceCoreCompatibleValues.Context.initial checked) plan globals (native.map (·.table))
      checked.catalog.definitions Core.Word.zero (some validationPlan) with
  | .error error => .error (.inputs error)
  | .ok context => .ok ⟨context, SourceCoreCompatibleInputs.prepare_values accepted⟩

structure Prepared (checked : Checked) where private mk ::
  sourceProgram : CheckedProgram
  signatureOwnership : checked.signatures = sourceProgram.signatures
  validationPlan : Plan
  plan : Plan
  locals : SourceCoreLocalPolymorphism.Catalog
  contexts : List SourceCoreLocalEvidence.Prepared
  functions : List SourceCoreGeneralFunctions.Function
  globals : List SourceCoreCalls.Signature
  closures : List Core.Expr
  callableContext : Option SourceCoreGeneralFunctions.CallableContext
  sourceInputs : Option (SourceInputs checked)
  diagnostics : Option (SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked))
  callableDiagnostics : Option SourceCoreCallableFaultSites.Program
  entries : List (Entry checked)

def Prepared.find? {checked : Checked} (prepared : Prepared checked) (key : Key) : Option (Entry checked) :=
  prepared.entries.find? (fun entry => decide (entry.key = key))

def representation (context : Values) (fuel : Nat) : SourceCoreGeneralFunctions.Representation := {
  expressions := SourceCoreCompatibleDataExpressions.functionPolicy fuel context
  allowStaged := context.checked.catalog.callableContracts
  loops := fun solved assignments diagnostics owner expression =>
    SourceCoreCompatibleDataMatches.loopPolicy context solved assignments diagnostics owner expression
  loopsWithSourceCells := fun cells solved assignments diagnostics owner expression =>
    SourceCoreCompatibleDataMatches.loopPolicy context solved assignments diagnostics owner expression cells
}

private def project (checked : Checked) (type : TypeSystem.Ty) :
    Except SourceCoreLocalPolymorphism.Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError fun
    | .catalog error => .projection error
    | .metadata _ => .projection (.unsupportedType type)

def prepareWithCatalog (program : CheckedProgram) (plan : Plan) (checked : Checked)
    (ownership : checked.signatures = program.signatures) (fuel : Nat) :
    Except Error (Prepared checked) := do
  let validationPlan := plan
  let plan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.plan
  let context := SourceCoreCompatibleValues.Context.initial checked
  let representation := representation context fuel
  let locals ← (SourceCoreLocalPolymorphism.prepareWithProjection (project checked) plan).mapError Error.locals
  let contexts ← (SourceCoreStageCodebook.prepareContexts program plan (locals.bindings.flatMap (·.instances)))
    |>.mapError Error.contexts
  let functions ← (plan.specializations.reverse.mapM
    (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation)).mapError Error.functions
  let globals := functions.map (·.signature)
  match plan.seedKeys with
  | [] => pure ⟨program, ownership, validationPlan, plan, locals, contexts,
      functions, globals, [], none, none, none, none, []⟩
  | first :: _ =>
      let diagnostics ← (SourceCoreCompatibleDataPlaceFaultSites.prepare context plan first
        (contexts.map (fun prepared => (prepared.caller.key, prepared.source)))).mapError Error.diagnostics
      let native ← if checked.catalog.callableContracts then do
          let table ← (SourceCoreStageCodebook.prepareWithProjection program plan (project checked)).mapError Error.contexts
          let callableDiagnostics ← (SourceCoreCallableFaultSites.prepare plan table diagnostics.program.rootTable
            diagnostics.nextReason).mapError Error.callables
          pure (some {table, diagnostics := callableDiagnostics : SourceCoreGeneralFunctions.CallableContext})
        else pure none
      let locals ← match native with
        | none => pure locals
        | some native => (locals.withCallableContracts (fun caller initializer active =>
            native.table.idAt? (.lambda caller initializer active))).mapError Error.locals
      let loweredDiagnostics := match native with
        | none => diagnostics.program
        | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}
      let closures ← (functions.mapM (SourceCoreGeneralFunctions.compileClosureWithRepresentation
        program representation program.signatures plan globals loweredDiagnostics locals native fuel)).mapError Error.functions
      let sourceInputs ← prepareSourceInputs checked plan validationPlan globals native
      let entries ← plan.seedKeys.mapM fun key => do
        let function ← match functions.find? (fun function => decide (function.signature.key = key)) with
          | some function => pure function
          | none => throw (.missingRoot key)
        let arguments := SourceCoreCalls.packArguments (function.inputs.zipIdx.map fun ((_, type), index) =>
          ⟨type, Core.OptionalCell.read type (.var (globals.length + (function.inputs.length - 1 - index))) Core.Word.zero⟩)
        let body ← (SourceCoreGeneralFunctions.assembleCall globals functions closures key arguments).mapError Error.functions
        let native ← (SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions (function.inputs.map Prod.snd)
          function.signature.resultType body).mapError Error.native
        pure (Entry.mk key (function.inputs.map Prod.fst) function.specialized.function.inferredBodyType native)
      pure ⟨program, ownership, validationPlan, plan, locals, contexts,
        functions, globals, closures, native, some sourceInputs, some diagnostics, native.map (·.diagnostics), entries⟩

structure Automatic where private mk ::
  checked : Checked
  prepared : Prepared checked

private def originalMetadata (source : TypedSource) : List SourceCoreRawMetadata.Metadata :=
  source.nodes.filterMap fun
    | .expression {form := .constructor instantiation _, ..} =>
        if SourceCoreDataCatalog.closed instantiation.resultType &&
            instantiation.payloadTypes.all SourceCoreDataCatalog.closed &&
            instantiation.parameterSubstitution.all (fun entry => SourceCoreDataCatalog.closed entry.2) then
          some (.constructor instantiation) else none
    | .expression {form := .proxy inner, ..} =>
        if SourceCoreDataCatalog.closed inner then some (.proxy inner) else none
    | _ => none

def prepare (program : CheckedProgram) (plan : Plan) (fuel : Nat)
    (limits : SourceCoreRawMetadata.Limits := {}) : Except Error Automatic := do
  let executable ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.plan
  let locals ← (SourceCompilationPlan.localLambdaCatalog executable).mapError
    (Error.locals ∘ SourceCoreLocalPolymorphism.Error.discovery)
  let sources := executable.specializations.map (·.function.typedBody) ++
    locals.map (fun candidate => candidate.source.applySubstitution candidate.substitution)
  let types := (SourceCorePlanCatalog.planTypes executable ++ sources.flatMap (fun source =>
    SourceCorePlanCatalog.sourceTypes source ++ source.nodes.filterMap (fun
      | .expression node => some node.rawType
      | _ => none))).filter SourceCoreDataCatalog.closed |>.eraseDups
  match accepted : SourceCoreCompatibleCatalog.prepare program.signatures fuel types
      (sources.flatMap originalMetadata) limits with
  | .error error => throw (.catalog error)
  | .ok checked =>
      let prepared ← prepareWithCatalog program plan checked
        (SourceCoreCompatibleCatalog.prepare_signatures accepted) fuel
      pure ⟨checked, prepared⟩

inductive RunError where
  | argumentCountMismatch (expected actual : Nat)
  | missingEntry (key : Key)
  | input (index : Nat) (error : SourceCoreCompatibleValues.Error)
  | native (error : SourceCoreGeneralEntry.RunError)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  | sourceInputsUnavailable
  | sourceInput (error : SourceCoreCompatibleInputs.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | compile (error : SourceCoreGeneralEntry.NativeCompileError)
  deriving Repr

private def encodeArguments (fuel : Nat) (context : Values) (index : Nat) :
    List TypedBinder → List DataValue → Except RunError (SourceCoreCompatibleValues.Extended context.registry (List Core.Value))
  | [], [] => pure (.pure context.registry [])
  | input :: inputs, value :: values => do
      let encoded ← (SourceCoreCompatibleValues.encode fuel context input.scheme.body value).mapError (RunError.input index)
      let rest ← encodeArguments fuel encoded.context (index + 1) inputs values
      pure ⟨rest.registry, encoded.preserves.trans rest.preserves, encoded.value :: rest.value⟩
  | inputs, values => throw (.argumentCountMismatch (index + inputs.length) (index + values.length))

structure Result {checked : Checked} (entry : Entry checked) where private mk ::
  context : Values
  contextOwner : context.checked = checked
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry context.registry
  diagnostics : SourceCoreFaultSites.Table
  native : NativeResult checked.catalog.definitions entry.native.resultType

private def diagnosticTable {checked : Checked} (prepared : Prepared checked) (entry : Entry checked)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry) :
    Except RunError SourceCoreFaultSites.Table := do
  let table ← match prepared.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry registry extension).mapError RunError.diagnostics
    | none => pure {
        owner := entry.key.declaration, resultType := entry.sourceResultType
        reads := [], escapedReason := Core.Word.zero }
  pure <| match prepared.callableDiagnostics with
    | none => table
    | some diagnostics => {table with additional := table.additional ++
        diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

private def runEntryData {checked : Checked} (prepared : Prepared checked) (entry : Entry checked)
    (arguments : List DataValue) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Result entry) := do
  let context := SourceCoreCompatibleValues.Context.initial checked
  let encoded ← encodeArguments validationFuel context 0 entry.inputs arguments
  let context := context.extend encoded.registry encoded.preserves
  let native ← (entry.native.run encoded.value executionFuel).mapError RunError.native
  let table ← diagnosticTable prepared entry encoded.registry encoded.preserves
  pure ⟨context, rfl, encoded.preserves, table, native⟩

structure Completion (checked : Checked) where private mk ::
  entry : Entry checked
  result : Result entry

def Prepared.runData {checked : Checked} (prepared : Prepared checked) (key : Key)
    (arguments : List DataValue) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Completion checked) := do
  let entry ← match prepared.find? key with
    | some entry => pure entry
    | none => throw (.missingEntry key)
  let result ← runEntryData prepared entry arguments executionFuel validationFuel
  pure ⟨entry, result⟩

/-- Source inputs retain the original validation plan. Only argument carriers
are injected below cached globals; source bodies and staging are already compiled. -/
def Prepared.runSource {checked : Checked} (prepared : Prepared checked) (key : Key)
    (arguments : List SourceTypedRuntime.Value) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Completion checked) := do
  let entry ← match prepared.find? key with
    | some entry => pure entry
    | none => throw (.missingEntry key)
  let ready ← match prepared.sourceInputs with
    | some ready => pure ready
    | none => throw .sourceInputsUnavailable
  let encoded ← (SourceCoreCompatibleInputs.encode ready.context (entry.inputs.map (·.scheme.body))
    arguments validationFuel).mapError RunError.sourceInput
  have extension : SourceCoreRawMetadata.Extends checked.staticRegistry encoded.values.registry := by
    change SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry _
    rw [← ready.valuesExact]
    exact encoded.preserves
  let context := (SourceCoreCompatibleValues.Context.initial checked).extend encoded.values.registry extension
  let body ← (SourceCoreGeneralFunctions.assembleCall prepared.globals prepared.functions prepared.closures
    key ⟨encoded.type, encoded.expression⟩).mapError RunError.functions
  let native ← match accepted : SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions []
      entry.native.resultType body with
    | .error error => throw (.compile error)
    | .ok runner =>
        let result ← (runner.run [] executionFuel).mapError RunError.native
        have resultType := (SourceCoreGeneralEntry.NativeEntry.compile_fields accepted).2.1
        pure (resultType ▸ result)
  let table ← diagnosticTable prepared entry encoded.values.registry extension
  pure ⟨entry, ⟨context, rfl, extension, table, native⟩⟩

def Completion.resume {checked : Checked} (completion : Completion checked) (fuel : Nat) : Completion checked :=
  match completion.result.native.checkpoint? with
  | none => completion
  | some checkpoint => ⟨completion.entry, {completion.result with native := checkpoint.resume fuel}⟩

end Solcore.Frontend.SourceCoreCompatibleFunctions
