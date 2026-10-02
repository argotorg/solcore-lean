import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodBodyMeaning

/-! A finite list retains actual method compilation, concrete body certificates
and independently selected source dictionaries. Runtime entries observe saved
closures and frame history only. No body execution law is a field. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev BodyOutcome := CallableCoercionMethodFrame.BodyOutcome

def allocationError (error : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error :=
  .sourceAllocation (reprStr error)

/-- Each row retains the actual compiler output and a concrete finite body
certificate. Source selection fixes one dictionary, without claiming its
uniqueness among all independently allowed source selections. Raw endpoint
and single-argument layout equations are independent static obligations. -/
structure Method {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (values : ValuesContext) (program : SourceSemantics.Program) (callerContext : SourceSemantics.Context)
    (callerEvidence : Dynamic.EvidenceEnvironment) where
  step : CoercionStep
  call : CallableCoercionSpine.Call
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Expr
  compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code
  signature : named.signature = call.signature
  sourceBody : Dynamic.BodyInstance
  function : Dynamic.Closure
  selected : Dynamic.OperatorMethodSelected program callerContext callerEvidence "Coerce" "coerce"
    step.requirements sourceBody function.evidence
  frame : CallableCoercionMethodFrame.Frame sourceBody function
  source : function.source = CallableIndexedNamedGeneration.source named
  statements : function.body = compiled.statements
  input : TypedBinder
  bindings : named.inputs = [(input, call.signature.parameterType)]
  parameters : function.parameters = [input]
  inputs : function.source.inputs = [input]
  inputType : input.scheme.body = step.source
  result : function.resultType = step.target
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  valid : CompatibleExpressionLiterals.ContextValid named.specialized.function.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source
  readFuel : Nat
  certificate : BuiltinNamedBody.Certificate prepared.layouts named.signature.key [] prepared.ancestry.layout.frame
    prepared.base.globals.length allocationError readFuel values function.source context named.specialized.function.solvedRequirements
    (diagnostics.reasonAt named.signature.key) (named.inputs.reverse.map fun binding => (binding.1.id, binding.2))
    function.body function.resultType named.signature.resultType
    (CompatibleNamedBody.bodyPolicy ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.sourceProgram prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
      diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext)
    prepared.fuel compiled.own.fellThroughReason compiled.own.table.escapedReason compiled.body

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment}
abbrev Methods := List (Method prepared values program callerContext callerEvidence)

variable {programSource : SourceSemantics.Program}

/-- Each row is tied to the real compiler Step, including the complete selected
specialization and ordered dictionary. Renaming affects only the caller slot;
it never changes the dictionary or a saved capture. -/
inductive Emitted (program : CheckedProgram) (project : SourceCoreEvidence.Projector)
    (compilation : SourceCoreFunctions.Context) (caller : SourceSpecialization.SpecializedFunction)
    (available : SourceCompilationPlan.EvidenceEnvironment) (scope : SourceCoreBasic.Scope)
    (node : ExpressionNode) (policy : SourceCoreFunctions.CallablePolicy) (ξ : Renaming) :
    SourceCoreBasic.LoweredExpr → Methods (prepared := prepared) (values := values) (program := programSource)
      (callerContext := callerContext) (callerEvidence := callerEvidence) → SourceCoreBasic.LoweredExpr →
    List CallableCoercionSpine.Call → Prop where
  | nil {input} : Emitted program project compilation caller available scope node policy ξ input [] input []
  | cons {input middle output call calls method methods}
      (step : CallableCoercionSpine.Step program project compilation caller available scope node policy input method.step middle call)
      (slot : method.call = call.rename ξ)
      (completeRecord : method.named.specialized = step.specialized)
      (dictionary : method.function.evidence = CallableNamedMetadata.environment step.dictionary)
      (tail : Emitted program project compilation caller available scope node policy ξ middle methods output calls) :
      Emitted program project compilation caller available scope node policy ξ input (method :: methods) output (call :: calls)

variable {programSource : SourceSemantics.Program} {compilerProgram : CheckedProgram}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {callerFunction : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}
  {input output : SourceCoreBasic.LoweredExpr}
  {profiles : Methods (prepared := prepared) (values := values) (program := programSource)
    (callerContext := callerContext) (callerEvidence := callerEvidence)} {calls : List CallableCoercionSpine.Call}

theorem Emitted.spine (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input profiles output calls) :
    CallableCoercionSpine.Spine compilerProgram project compilation callerFunction available scope node policy input (profiles.map (·.step)) output calls := by
  induction emitted with
  | nil => exact .nil
  | cons step _ _ _ tail ih => exact .cons step ih

theorem Emitted.calls_eq (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input profiles output calls) :
    profiles.map (·.call) = calls.map (CallableCoercionSpine.Call.rename ξ) := by
  induction emitted with
  | nil => rfl
  | cons step slot _ _ tail ih => simp only [List.map_cons, slot, ih]

/-- Actual capture values are never renamed; the saved body syntax and capture
lookup embedding are retained separately. -/
structure Capture (method : Method prepared values program callerContext callerEvidence)
    (definitions : DataEnvironment) (frameLocation : Location) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative [] [] canonical definitions
  locals : Dynamic.EnvironmentAgrees heap method.function.context.locals []
  layout : EnvironmentsAgree embedding canonical captured
  typed : RuntimeEnvironmentHasTypes world captured capturedContext definitions
  reference : canonical[prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  capturedReference : captured[embedding prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  installed : CallableCoercionMethodBody.Installed method.call method.compiled.output embedding.lift caller captured store
  unmapped : installed.location ∉ mapping

structure Entry (methods : Methods (prepared := prepared) (values := values) (program := program)
      (callerContext := callerContext) (callerEvidence := callerEvidence))
    (definitions : DataEnvironment) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  frameLocation : Location
  unmapped : frameLocation ∉ mapping
  typed : world[frameLocation]? = some prepared.ancestry.layout.frame.type
  current : NativeFrame
  ghost : GhostFrame
  frame : CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
    frameLocation current ghost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame mapping store records
  captures : ∀ method, method ∈ methods → Nonempty (Capture method definitions frameLocation caller mapping world heap store)

variable {methods : Methods (prepared := prepared) (values := values) (program := program)
    (callerContext := callerContext) (callerEvidence := callerEvidence)}
  {definitions : DataEnvironment} {caller : Environment}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store futureStore : Store}

/-- Source heap effects preserve every protected global cell, including later
methods. The proof uses the original full stored closure and captures. -/
def Capture.extend {method : Method prepared values program callerContext callerEvidence} {location : Location}
    (capture : Capture method definitions location caller mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Capture method definitions location caller futureMap futureWorld after futureStore := by
  have retained := frame capture.installed.location capture.unmapped (List.getElem?_eq_some_iff.mp capture.installed.read).1
  exact { capture with
    environments := capture.environments.extend maps worlds
    locals := capture.locals.mono metadata
    typed := capture.typed.weaken worlds
    installed := {capture.installed with read := retained.2.trans capture.installed.read}
    unmapped := retained.1 }

def Entry.extend (entry : Entry methods definitions caller mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Entry methods definitions caller futureMap futureWorld after futureStore := by
  have retained := frame entry.frameLocation entry.unmapped (List.getElem?_eq_some_iff.mp entry.frame.read).1
  refine { entry with
    unmapped := retained.1
    typed := worlds.lookup entry.typed
    frame := ⟨retained.2.trans entry.frame.read, entry.frame.history⟩
    snapshots := entry.snapshots.transport frame
    captures := ?_ }
  intro method member
  obtain ⟨capture⟩ := entry.captures method member
  exact ⟨capture.extend maps worlds frame metadata⟩

def Entry.restrict {subset : Methods (prepared := prepared) (values := values) (program := program)
      (callerContext := callerContext) (callerEvidence := callerEvidence)}
    (entry : Entry methods definitions caller mapping world heap store)
    (included : ∀ method ∈ subset, method ∈ methods) :
    Entry subset definitions caller mapping world heap store :=
  {entry with captures := fun method member => entry.captures method (included method member)}

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEntries
