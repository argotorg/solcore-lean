import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.Frontend.SourceCoreUnified
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LoopAndMatchBounds
import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.Frontend.Internal.RuntimeValidation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds

/-!
# Owned callables: ready bodies and origins

Ready entries and catalogs of bodies, origin and nested canonical state, the public signature catalog and diagnostic receipts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
/-! Public compiler receipts retain the actual diagnostic preparation and its
selected specialization Source. This is static metadata provenance; Source
execution and body meaning are not premises. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- The compatible place pass keeps the actual program fault inventory. -/
theorem data_place_base {context : SourceCoreCompatibleValues.Context}
    {plan : SourceSpecializationWorklist.Plan} {root : SourceSpecialization.SpecializationKey}
    {sources : List (SourceSpecialization.SpecializationKey × TypedSource)}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok diagnostics) :
    SourceCoreProgramFaultSites.prepare plan root = .ok diagnostics.program.base := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
  obtain ⟨state, _stateMade, accepted⟩ := bind_ok accepted
  obtain ⟨extra, _extraMade, accepted⟩ := bind_ok accepted
  cases accepted
  exact mapError_ok baseMade

/-- The actual compatible compiler's nonempty diagnostic receipt is the
successful place preparation for its retained executable plan. -/
theorem compatible_diagnostics {source : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = source.signatures}
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog source plan checked ownership fuel = .ok prepared)
    (found : prepared.diagnostics = some diagnostics) :
    ∃ root sources, SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial checked)
      prepared.plan root sources = .ok diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _executableMade, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _localsMade, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _contextsMade, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _functionsMade, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    cases found
  · obtain ⟨actual, actualMade, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _tableMade, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _callableMade, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _nativeLocalsMade, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _closuresMade, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _inputsMade, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _entriesMade, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨_, _, mapError_ok actualMade⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _closuresMade, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _inputsMade, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _entriesMade, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨_, _, mapError_ok actualMade⟩

/-- Catalog preparation preserves that same actual diagnostic producer. -/
theorem automatic_diagnostics {source : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked)}
    (accepted : SourceCoreCompatibleFunctions.prepare source plan fuel = .ok automatic)
    (found : automatic.prepared.diagnostics = some diagnostics) :
    ∃ root sources, SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial automatic.checked)
      automatic.prepared.plan root sources = .ok diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _executableMade, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _localsMade, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
    cases accepted
    exact compatible_diagnostics baseMade found

/-- The sealed indexed compilation retains the original compatible diagnostic
inventory, rather than a second table inferred from equal native code. -/
theorem compiled_diagnostics (compiled : SourceCoreUnifiedCompilation.Compiled)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics) :
    ∃ root sources, SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
      compiled.indexed.base.plan root sources = .ok diagnostics := by
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared] at found ⊢
  exact automatic_diagnostics compiled.compatiblePrepared found

/-- The lowered table is exactly the real second-pass table, with only the
actual callable root diagnostic replacement allowed by the compiler. -/
structure Receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row) : Prop where
  actual : ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
    compiled.indexed.base.diagnostics = some diagnostics ∧
    prepared.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}

/-- Exact cached hook authority authenticates the same specialization Source
whose actual diagnostic row supplies this prepared assignment table. -/
theorem assignments_prepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
    (receipt : Receipt prepared) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare
      prepared.named.specialized.function.typedBody first = .ok prepared.compilation.own.assignments := by
  obtain ⟨diagnostics, found, lowered⟩ := receipt.actual
  obtain ⟨root, sources, made⟩ := compiled_diagnostics compiled found
  have programMade := data_place_base made
  have selected : diagnostics.program.base.find? prepared.named.signature.key = some prepared.compilation.own := by
    have selected := prepared.compilation.diagnostic
    have sameBase : prepared.diagnostics.base = diagnostics.program.base := by
      rw [lowered]
      cases compiled.indexed.base.callableContext <;> rfl
    rw [sameBase] at selected
    exact selected
  exact SourceCoreProgramFaultSites.prepare_assignments_at programMade
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook) selected

/-- Public preparation chooses the same actual second-pass compiler receipt
and retains its diagnostic identity. Existing Prepared values remain unchanged. -/
theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations) :
    ∃ prepared : Prepared recipe.compiled row, Receipt prepared := by
  obtain ⟨programEq, origins⟩ := public_origins accepted issued
  obtain ⟨index, named, selected, same⟩ := cached_row recipe.compiled member
  obtain ⟨diagnostics, code, actual, cached, compiledCode⟩ := NamedCalls.compiled_at recipe.compiled.indexed selected
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted recipe.compiled.indexed compiledCode
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled
  obtain ⟨growth, covered⟩ := CallableCoercionPreparation.of_accepted prepared
  obtain ⟨available, resolved, _⟩ := covered row (growth.entries.subset member)
  let result : Prepared recipe.compiled row := ⟨index, named, _, code, compilation, available, selected, same, cached,
    by simpa only [programEq] using origins row member, resolved⟩
  exact ⟨result, ⟨⟨diagnostics, actual, rfl⟩⟩⟩

/-- A genuine Header alignment gives the assignment preparation equation
at the same full Header Source used by static profile extraction. -/
theorem assignments_at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
    (receipt : Receipt prepared) {instantiation : DeclarationInstantiation}
    {values : SourceCoreCompatibleValues.Context}
    {header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare header.function.source first =
      .ok prepared.compilation.own.assignments := by
  have source : header.function.source = prepared.named.specialized.function.typedBody := by
    rw [aligned.function]
    rfl
  rw [source]
  exact assignments_prepared prepared receipt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyTypedFacts
/-! The original parameter receipt supplies genuine Source body typing.
Compiler syntax remains a separate static receipt for the same context, roots
and result type. Their conjunction supplies the actual imperative input facts;
it contains no execution or recursive body meaning premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyTypedFacts
open Frontend SourceInference

variable {program : Program} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}

/-- Keep the original Source control judgment at the actual parameter context. -/
theorem statements
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Statements function.source context function.body := by
  obtain ⟨finalContext, facts, typed, _completes⟩ := receipt.bodyTyped
  exact ⟨{ returnType := function.resultType }, finalContext, facts, typed⟩

/-- Authenticate body input facts from the Source receipt and original syntax.
No native type or erased compiler body recovers the Source judgment. -/
theorem facts {expressionSyntax : ExpressionId → Prop}
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function context environment heap)
    (syntaxTree : GenericImperativeMatch.Syntax function.source expressionSyntax context
      (.statements true function.body) function.resultType) :
    ProtectedStateImperativeTypedSourceSites.Facts function.source expressionSyntax
      context true function.body function.resultType :=
  ⟨syntaxTree, statements receipt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyTypedFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries
/-! Genuine parameter Source receipts and every original row authenticate the
same actual body entry. Independent compiler syntax supplies its static facts;
the ready origin wrapper forwards the complete entry without rebuilding it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {condition : Location → NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}

def entry
    (original : CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := origin) (functions := functions))
    (syntaxTree : GenericImperativeMatch.Syntax origin.function.source origin.expressionSyntax origin.context
      (.statements true origin.function.body) origin.function.resultType) :
    CallableRuntimeBodyReadyOrigins.Entry callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      condition (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      origin functions :=
  ⟨original.original, CallableIndexedOwnedBodyTypedFacts.facts original.source syntaxTree, original.admission⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
/-! The original compiler body retains its code, sites, Source and reached
entry. Its visited validity domain also carries authentic Source runtime
facts. The initial receipt supplies these facts; binder extension transports
only the static non-local fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableRuntimeBodyOrigins
universe u v

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {program : Program} (origin : StaticOrigin values ambient registry faults)
  (runtime : Dynamic.SourceRuntimeValid program origin.context origin.function.source)

/-- Strengthening the static domain does not change the compiled body. -/
def source_origin : StaticOrigin values ambient registry faults where
  layouts := origin.layouts
  owner := origin.owner
  active := origin.active
  frameLayout := origin.frameLayout
  globals := origin.globals
  onError := origin.onError
  function := origin.function
  expressionSyntax := origin.expressionSyntax
  certificates := origin.certificates
  validity := fun context => origin.validity context ∧
    Dynamic.SourceRuntimeValid program context origin.function.source
  diagnosticPolicy := origin.diagnosticPolicy
  administrative := origin.administrative
  context := origin.context
  scope := origin.scope
  output := origin.output
  code := origin.code
  fellThrough := origin.fellThrough
  escaped := origin.escaped
  solved := origin.solved
  body := {
    flow := origin.body.flow
    tree := origin.body.tree
    sites := origin.body.sites
    initialValid := ⟨origin.body.initialValid, runtime⟩
    projection := origin.body.projection
    unique := origin.body.unique
    emitted := origin.body.emitted
  }
  definitions := origin.definitions
  registered := origin.registered
  escapedFault := origin.escapedFault
  extend := fun ⟨valid, sourceValid⟩ extended =>
    ⟨origin.extend valid extended,
      sourceValid.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)⟩
  runtimeOf := fun valid => origin.runtimeOf valid.1

/-- The original complete actual entry is repacked field for field. -/
def entry {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {condition : Location → CallableIndexedHistory.NativeFrame → Prop}
    {functions : FunctionModel values.checked.catalog ambient}
    (original : Stateful.Entry protocol condition origin functions) :
    Stateful.Entry protocol condition (source_origin origin runtime) functions where
  mapping := original.mapping
  world := original.world
  environment := original.environment
  canonical := original.canonical
  actual := original.actual
  heap := original.heap
  store := original.store
  embedding := original.embedding
  actualContext := original.actualContext
  frameLocation := original.frameLocation
  native := original.native
  environments := original.environments
  heaps := original.heaps
  locals := original.locals
  lookups := original.lookups
  actualTyped := original.actualTyped
  reference := original.reference
  read := original.read
  unmapped := original.unmapped
  initial := original.initial
  gate := original.gate

theorem entry_initial {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {condition : Location → CallableIndexedHistory.NativeFrame → Prop}
    {functions : FunctionModel values.checked.catalog ambient}
    (original : Stateful.Entry protocol condition origin functions) :
    (entry origin runtime original).initial = original.initial := rfl

theorem source_code : (source_origin origin runtime).code = origin.code := rfl

theorem source_function : (source_origin origin runtime).function = origin.function := rfl

section Owned
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {condition : Location → CallableIndexedHistory.NativeFrame → Prop}
  {originalOrigin : StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}

def admitted_entry
    (original : CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := originalOrigin) (functions := functions)) :
    CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := source_origin originalOrigin original.source.runtime) (functions := functions) :=
  ⟨entry originalOrigin original.source.runtime original.original, original.source, original.rows⟩

def ready_entry
    (original : CallableIndexedOwnedAdmittedBodyEntries.Entry bridge
      (condition := condition) (origin := originalOrigin) (functions := functions))
    (syntaxTree : GenericImperativeMatch.Syntax originalOrigin.function.source originalOrigin.expressionSyntax originalOrigin.context
      (.statements true originalOrigin.function.body) originalOrigin.function.resultType) :
    CallableRuntimeBodyReadyOrigins.Entry callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      condition (ProtectedStateImperativeTypedSourceSites.Facts originalOrigin.function.source originalOrigin.expressionSyntax)
      (source_origin originalOrigin original.source.runtime) functions :=
  CallableIndexedOwnedBodyReadyEntries.entry bridge (admitted_entry bridge original) syntaxTree

end Owned
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaViewHeads
/-! Lambda compiler views retain their actual named-call emission and exact
selected slots. Nested formation uses the reached owner's own history and
complete original captures, while leaving its actual pool unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaViewHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}

theorem view_preserves_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : Below budget (PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix certificate))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) size := by
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.preserves_at_with functions owner sameLayouts conditions authorized
      budget size within idsUnique unique owners argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed initial globals trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have independent := RecursiveNamedArgumentTraceBounds.source_inv receipt.metadata receipt.form receipt.calleeFound
      receipt.predicates receipt.evidenceEmpty unique trace
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_preserves_bounded_with functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget argumentMeaning (bodyMeaning receipt.header receipt.member) owners receipt.member
        initial globals environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot]
      exact evaluated
    · simpa only [receipt.sourceType, receipt.nativeType] using represented

theorem view_reflects_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix certificate))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) size := by
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.reflects_at_with functions owner sameLayouts conditions authorized
      budget size within argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed initial globals evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_reflects_bounded_with functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget argumentMeaning (bodyMeaning receipt.header receipt.member) receipt.member
        initial globals environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro receipt.metadata receipt.form receipt.calleeFound
      receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid receipt.predicates receipt.evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [receipt.sourceType, receipt.nativeType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata, transition⟩

section Formation
open CallableIndexedLambdaNestedRuntimeBodyMeaning
open RecursiveNamedLambdaFormationHeads
variable {caller : CallableIndexedOwnedFunctionValues.Header compiled program}
  {rank : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}

/-- The real reached Current receipt supplies its own ghost. Stable lookup
uniqueness fixes the full original metadata without identifying ghost histories. -/
theorem carries_of_stable_read
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame native)) :
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost metadata := by
  have encoded := Option.some.inj ((CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position).symm.trans read)
  have current : (initial.rows owner.position).authority.current = native := by
    have decoded := congrArg (decode compiled.indexed.ancestry.layout.frame) encoded
    simpa only [decode_encode, Option.some.injEq] using decoded
  have actualHistory := (initial.rows owner.position).authority.frame.history
  rw [current] at actualHistory
  cases stable with
  | empty =>
    cases actualHistory with
    | stable carried =>
      have same := Option.some.inj (carried.lookup.symm.trans (Carries.empty (inputs := compiled.indexed.ancestry.graph.inputs) (table := compiled.indexed.ancestry.graph.table)).lookup)
      simpa only [current, same] using carried
  | state stored history =>
    cases actualHistory with
    | stable carried =>
      have same := Option.some.inj (carried.lookup.symm.trans (Carries.state stored history).lookup)
      simpa only [current, same] using carried

/-- Original canonical frame/bundle observations are combined with the exact
selected authority, including its complete ordered records and own ghost. -/
def nested_entry
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked)
      caller headers owner.key.locations 0 1 scope mapping world heap store canonical :=
  { catalog := {
      authority := {
        frameLocation := (initial.rows owner.position).authority.frameLocation
        unmapped := (initial.rows owner.position).authority.unmapped
        typed := (initial.rows owner.position).authority.typed
        current := (initial.rows owner.position).authority.current
        ghost := (initial.rows owner.position).authority.ghost
        frame := (initial.rows owner.position).authority.frame
        records := (initial.rows owner.position).authority.records
        snapshots := (initial.rows owner.position).authority.snapshots
        distinct := (initial.rows owner.position).authority.distinct
        captures := by
          intro header member
          have capture := (initial.rows owner.position).authority.captures header member
          change Nonempty (Capture headers owner.key.locations owner.key.capturePrefix
            (initial.rows owner.position).authority.frameLocation header mapping world heap store) at capture
          simpa only [prefixZero] using capture }
      globals := observed.globals }
    history := history
    bundle := bundle
    reference := by
      change canonical[scope.length + 1 + caller.globals]? = some
        (.cellRef compiled.indexed.ancestry.layout.frame.type (initial.rows owner.position).authority.frameLocation)
      rw [(initial.rows owner.position).frame_eq]
      change canonical[scope.length + 1 + caller.globals]? = some
        (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation)
      simpa only [globals] using observed.reference }

theorem nested_entry_current
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.current =
      (initial.rows owner.position).authority.current := by
  rfl

theorem nested_entry_ghost
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.ghost =
      (initial.rows owner.position).authority.ghost := by
  rfl

theorem nested_entry_records
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.records =
      (initial.rows owner.position).authority.records := by
  rfl

theorem nested_entry_frame
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.frameLocation =
      owner.key.frameLocation := by
  exact (initial.rows owner.position).frame_eq

/-- Formation uses the original supported nested body and authentic current
metadata. Its native closure captures the copies of the captured cells; the
copies extend the store, and no row's records change. The represented closure
is transferred forward into any including function model. -/
theorem formation_in
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    (inclusion : (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile).Includes functions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store) :
    ∃ value captured finalHeap finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (formed head captured)) finalHeap ∧
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap captured
        finalHeap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) finalStore ∧
      CompatiblePayload.ValueRep compiled.compatible.checked registry functions
        finalMap finalWorld head.code.sourceNode.type (.closure (formed head captured)) value lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld finalHeap
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap finalHeap ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, finalHeap, finalStore, canonical⟩ := by
  let entry := nested_entry initial owner prefixZero observed history bundle globals
  let captured : Captures compiled.indexed mapping world scope environment actual :=
    captures_for complete globals entry related agrees typed
  let code : Code compiled.indexed (formed head environment) scope captured.administrative := actualCode head environment
  let currentHistory : History code := historyAt head entry environment
  let body : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code := actualSupport head environment
  have origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code currentHistory body :=
    CallableIndexedOwnedFunctionValues.ActualSourceOrigin.of_nested head entry environment
  have captureGlobals := capture_globals_for complete globals slots entry related agrees typed
  have captureGlobals' : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    have frame : entry.catalog.authority.frameLocation = owner.key.frameLocation := by
      exact (initial.rows owner.position).frame_eq
    simpa only [frame] using captureGlobals
  have current : (initial.rows owner.position).authority.current = currentHistory.native := by
    rfl
  have ghost : (initial.rows owner.position).authority.ghost = currentHistory.ghost := by
    rfl
  obtain ⟨formedRecord, sourceValue, native, represented, _determined⟩ :=
    CallableIndexedOwnedFunctionValues.lambda_of_formation (compiled := compiled) (program := program)
      (headers := headers) (keys := keys) (function := formed head environment) initial owner captured code currentHistory body origin
      captureGlobals' (reference_index head) current ghost profile heaps head.snapshots
      (by change Dynamic.OrdinaryRequirementLayout head.code.sourceNode.requirements head.code.sourceNode.coercions []
          rw [head.requirements, head.coercions]; rfl) head.coercions
  refine ⟨CallableIndexedLambdaValues.value code formedRecord.embedding currentHistory.native formedRecord.closureActual,
    formedRecord.captured, formedRecord.finalHeap, formedRecord.finalStore, formedRecord.finalMap,
    formedRecord.finalWorld, ?_, formedRecord.copy, ?_, ?_, formedRecord.heaps, formedRecord.maps, formedRecord.worlds,
    formedRecord.frame, formedRecord.copy.metadata_extends,
    ProtectedStateTransition.AdministrativeTransport.transition (protocol headers keys)
      (administrativeTransport headers keys) initial formedRecord.maps formedRecord.worlds formedRecord.frame
      formedRecord.copy.metadata_extends⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
      environment heap head.code.id (.closure (formed head formedRecord.captured)) formedRecord.finalHeap at sourceValue
    simpa only [head.identifier] using sourceValue
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (CallableIndexedLambdaValues.value code formedRecord.embedding currentHistory.native
        formedRecord.closureActual)) formedRecord.finalStore)
      (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression.rename ξ) head.emitted)) native
  · rw [head.sourceType, head.nativeType]
    exact .function (inclusion represented)

/-- Formation in the owned function model itself. -/
theorem formation
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store) :
    ∃ value captured finalHeap finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (formed head captured)) finalHeap ∧
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap captured
        finalHeap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) finalStore ∧
      CompatiblePayload.ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        finalMap finalWorld head.code.sourceNode.type (.closure (formed head captured)) value lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld finalHeap
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap finalHeap ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, finalHeap, finalStore, canonical⟩ :=
  formation_in head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
    (fun represented => represented) heaps

theorem formation_preserves
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    (unique : NodeOccurrencesUnique source) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.code.sourceNode.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  let code : Code compiled.indexed (formed head environment) scope (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program) caller) := actualCode head environment
  have emptyCoercions : code.sourceNode.coercions = [] := head.coercions
  rw [sameSource] at unique trace
  cases trace.sound with
  | value evaluated =>
    rename_i result
    have original : Dynamic.ExpressionEvaluates program (formed head environment).context (formed head environment).evidence
        (formed head environment).source environment heap code.id result after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using evaluated
    obtain ⟨captured, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := program) (function := formed head environment) (scope := scope) (administrative := nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program) caller)
      code unique emptyCoercions original
    obtain ⟨value, formedCaptured, finalHeap, finalStore, finalMap, finalWorld, _source, formedCopy, native, represented,
        finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
      formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed heaps
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
    exact ⟨.inRight .word value, finalStore, finalMap, finalWorld, native, .value represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩
  | fault failed =>
    rename_i reason
    have original : Dynamic.ExpressionFaults program (formed head environment).context (formed head environment).evidence
        (formed head environment).source (formed head environment).captured heap code.id reason after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using failed
    exact False.elim (excludes_fault_of_code (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := program) (function := formed head environment) (scope := scope) (administrative := nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program) caller)
      code unique emptyCoercions original)

theorem formation_reflects
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.code.sourceNode.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨nativeValue, captured, finalHeap, formedStore, finalMap, finalWorld, sourceValue, _, native, represented,
      finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed heaps
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
      (.value (.closure (formed head captured))) finalHeap := by
    simpa only [sameSource] using (Dynamic.ExpressionEvaluatesOutcome.value sourceValue)
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  exact ⟨sourceSize, _, finalHeap, finalMap, finalWorld, sized, .value represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩

end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaViewHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOriginCanonicalState
/-! The emitted compiler function supplies a bundle type and full named seed.
Its independent Source origin remains in the authentic higher receipt. Actual
reached pools and their own ghosts remain intact through allocation and scope
restoration; no top-level Source Header is required. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOriginCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedExpressionHeads (Globals)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (principal : SourceCoreGeneralFunctions.Function)

/-- Full canonical frame and bundle observations remain independent of pool
ownership. Authentication uses the reached selected row's own ghost. -/
structure Packet (index : ProtectedStateTransition.Index)
    (initial : State headers keys index) : Prop where
  globals : Globals (headers := headers) owner 1 index.scope index.canonical
  reference : index.canonical[index.scope.length + 1 + compiled.indexed.base.globals.length]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation)
  bundle : (index.canonical.map Value.type)[index.scope.length]? = some principal.signature.parameterType
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
    (some (CallableIndexedNamedGeneration.state principal))

def protocol : ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { initial : State headers keys index // Packet owner principal index initial }
  records := fun initial => records initial.val
  Relates := fun initial reached => Relates initial.val reached.val
  refl := fun initial => Relates.refl initial.val
  trans := fun first last => first.trans last

/-- Only proofs are added: these are the original complete ordered lists. -/
theorem records_eq {index : ProtectedStateTransition.Index}
    (initial : (protocol (headers := headers) owner principal).State index) :
    (protocol owner principal).records initial = records initial.val := rfl

/-- The actual metadata/read packet supplies the original formation input. -/
theorem Packet.observed {index : ProtectedStateTransition.Index} {initial : State headers keys index}
    (packet : Packet owner principal index initial) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 index.scope index.canonical owner.key.frameLocation :=
  ⟨packet.globals, packet.reference⟩

/-- An authentic original stable read and the real environment prefix build
the entire packet at the selected actual pool, including its own ghost. -/
theorem packet_of_stable_read {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative : Core.Context} {environment : Dynamic.Environment}
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (leading : administrative[0]? = some principal.signature.parameterType)
    {native : NativeFrame} {ghost : GhostFrame}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost
      (some (CallableIndexedNamedGeneration.state principal)))
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame native)) :
    Packet owner principal _ initial :=
  ⟨observed.globals, observed.reference,
    (by
      rw [related.runtime_hasTypes.type_tags]
      simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using leading),
    CallableIndexedOwnedLambdaViewHeads.carries_of_stable_read initial owner stable read⟩

/-- A real administrative effect keeps the actual input frame read. The
returned pool's own Current proof authenticates its full original metadata. -/
theorem Packet.after {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store}
    {initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    (packet : Packet owner principal _ initial)
    (reached : State headers keys ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    Packet owner principal _ reached := by
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have bound := (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨_unmapped, unchanged⟩ := frame owner.key.frameLocation unmapped bound
  exact ⟨packet.globals, packet.reference, packet.bundle,
    CallableIndexedOwnedLambdaViewHeads.carries_of_stable_read reached owner packet.carried (unchanged.trans read)⟩

/-- Prepending the actual lexical value shifts all original canonical slots
and the bundle together; the actual pool and history are the same witness. -/
theorem Packet.prepend {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    (packet : Packet owner principal _ initial) (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Packet owner principal ⟨(id, type) :: scope, mapping, world, heap, store, value :: canonical⟩ initial := by
  refine ⟨CallableIndexedOwnedCanonicalState.globals_prepend owner 1 packet.globals id type value, ?_, ?_, packet.carried⟩
  · have offset : ((id, type) :: scope).length + 1 + compiled.indexed.base.globals.length =
        scope.length + 1 + compiled.indexed.base.globals.length + 1 := by simp; omega
    rw [offset]
    exact packet.reference
  · simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using packet.bundle

/-- Removing that same lexical slot restores the original observations while
retaining the actual reached pool, history and complete record lists. -/
theorem Packet.restore {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    {initial : State headers keys ⟨(id, type) :: scope, mapping, world, heap, store, value :: canonical⟩}
    (packet : Packet owner principal _ initial) :
    Packet owner principal ⟨scope, mapping, world, heap, store, canonical⟩ initial := by
  refine ⟨CallableIndexedOwnedCanonicalState.globals_restore owner 1 packet.globals, ?_, ?_, packet.carried⟩
  · have offset : ((id, type) :: scope).length + 1 + compiled.indexed.base.globals.length =
        scope.length + 1 + compiled.indexed.base.globals.length + 1 := by simp; omega
    have reference := packet.reference
    rw [offset] at reference
    exact reference
  · have bundle := packet.bundle
    simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using bundle

/-- An existing actual transition is wrapped at the same returned pool; its
real administrative preservation supplies the additional observations. -/
theorem transition_of_reached {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store}
    (initial : (protocol (headers := headers) owner principal).State ⟨scope, mapping, world, heap, store, canonical⟩)
    (transition : ProtectedStateTransition.Transition (CallableIndexedOwnedFunctionState.protocol headers keys) initial.val
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    ProtectedStateTransition.Transition (protocol owner principal) initial
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩ := by
  obtain ⟨reached, related⟩ := transition
  exact ⟨⟨reached, initial.property.after owner principal reached frame⟩, related⟩

def administrativeTransport : ProtectedStateTransition.AdministrativeTransport (protocol (headers := headers) owner principal) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    let reached := (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).extend state.val maps worlds frame metadata
    ⟨reached, Packet.after owner principal state.property reached frame⟩
  related := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).related state.val maps worlds frame metadata
  records_eq := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).records_eq state.val maps worlds frame metadata

def bindings : ProtectedStateTransition.Bindings (protocol (headers := headers) owner principal) where
  prepend := fun state id type value => ⟨state.val, Packet.prepend owner principal state.property id type value⟩
  prepend_related := fun state _ _ _ => Relates.refl state.val
  prepend_records := fun _ _ _ _ => rfl
  restore := fun state => ⟨state.val, Packet.restore owner principal state.property⟩
  restore_related := fun state => Relates.refl state.val
  restore_records := fun _ => rfl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

/-- The genuine marked allocator's real reached pool and actual prepended
reference supply the new packet. Its complete record-producing post is kept. -/
def markedProducer : ProtectedStateTransition.MarkedAllocation.Producer
    (protocol (headers := headers) owner principal) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native => (CallableIndexedOwnedMarkedAllocation.producer headers keys model).Ready state.val location native
  complete := by
    intro allocationOwner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, transition⟩ :=
      (CallableIndexedOwnedMarkedAllocation.producer headers keys model).complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.val ready
    obtain ⟨reached, related⟩ := transition
    have retained : Packet owner principal ⟨request.scope, _, _, after, _, canonical⟩ reached :=
      Packet.after owner principal initial.property reached frame
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨reached, Packet.prepend owner principal retained request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩⟩

theorem readyAt_of_stableOwner {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (markedProducer (headers := headers) owner principal model).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.val read

/-- The caller bridge restores the same actual pool using its real retained
frame read, preserving all complete ordered records. -/
def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier
    (headers := headers) (fun index => Globals (headers := headers) owner 1 index.scope index.canonical) (protocol (headers := headers) owner principal) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property.globals
  restore := by
    intro index initial mapping world heap store reached maps worlds frame metadata related
    exact ⟨⟨reached, Packet.after owner principal initial.property reached frame⟩, rfl, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOriginCanonicalState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
/-! The accepted public compiler retains its actual compatible catalog factory.
The same selected catalog therefore has the Source closure invariant proved by
registration. Catalog ownership comes from the factory equation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
open Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The real compatible factory selects this exact catalog from its actual
prepared Source type and metadata inventory. -/
theorem automatic_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {limits : SourceCoreRawMetadata.Limits}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel limits = .ok automatic) :
    ∃ types metadata, SourceCoreCompatibleCatalog.prepare program.signatures fuel types metadata limits true =
      .ok automatic.checked := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _executableMade, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _localsMade, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, _baseMade, accepted⟩ := bind_ok accepted
    cases accepted
    exact ⟨_, _, by assumption⟩

/-- The sealed public compilation keeps its exact successful catalog factory;
no equality of projected native definitions is used to recover ownership. -/
theorem compiled_catalog (compiled : SourceCoreUnifiedCompilation.Compiled) :
    ∃ types metadata, SourceCoreCompatibleCatalog.prepare compiled.sourceProgram.signatures
      compiled.compilationFuel types metadata {} true = .ok compiled.compatible.checked :=
  automatic_catalog compiled.compatiblePrepared

/-- Actual public preparation proves closure of the selected catalog entries. -/
theorem compiled_closed (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CompatibleCatalogRegistrationPrefix.ClosedSources compiled.compatible.checked.catalog := by
  obtain ⟨types, metadata, accepted⟩ := compiled_catalog compiled
  exact CompatibleCatalogClosedSources.prepare_closed accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
/-! Original nested formation observations accompany the actual pool through
lexical allocation and scope restoration. Reached history is authenticated by
its own Current receipt and a genuinely retained stable read. This wrapper
changes neither the ordered record observation nor the actual pool relation. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedExpressionHeads (Globals)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)

/-- Full canonical frame and bundle observations remain independent of pool
ownership. Authentication uses the reached selected row's own ghost. -/
structure Packet (index : ProtectedStateTransition.Index)
    (initial : State headers keys index) : Prop where
  globals : Globals (headers := headers) owner 1 index.scope index.canonical
  reference : index.canonical[index.scope.length + 1 + compiled.indexed.base.globals.length]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation)
  bundle : (index.canonical.map Value.type)[index.scope.length]? = some caller.named.signature.parameterType
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
    (some (CallableIndexedNamedGeneration.state caller.named))

def protocol : ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { initial : State headers keys index // Packet owner caller index initial }
  records := fun initial => records initial.val
  Relates := fun initial reached => Relates initial.val reached.val
  refl := fun initial => Relates.refl initial.val
  trans := fun first last => first.trans last

/-- Only proofs are added: these are the original complete ordered lists. -/
theorem records_eq {index : ProtectedStateTransition.Index}
    (initial : (protocol (headers := headers) owner caller).State index) :
    (protocol owner caller).records initial = records initial.val := rfl

/-- The actual metadata/read packet supplies the original formation input. -/
theorem Packet.observed {index : ProtectedStateTransition.Index} {initial : State headers keys index}
    (packet : Packet owner caller index initial) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 index.scope index.canonical owner.key.frameLocation :=
  ⟨packet.globals, packet.reference⟩

/-- An authentic original stable read and the real environment prefix build
the entire packet at the selected actual pool, including its own ghost. -/
theorem packet_of_stable_read {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative : Core.Context} {environment : Dynamic.Environment}
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (leading : administrative[0]? = some caller.named.signature.parameterType)
    {native : NativeFrame} {ghost : GhostFrame}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame native)) :
    Packet owner caller _ initial :=
  ⟨observed.globals, observed.reference,
    CallableIndexedLambdaNestedFormationEntries.bundle_of_environment (values := .initial compiled.compatible.checked)
      (indexed := compiled.indexed) (caller := caller) related leading,
    CallableIndexedOwnedLambdaViewHeads.carries_of_stable_read initial owner stable read⟩

/-- A real administrative effect keeps the actual input frame read. The
returned pool's own Current proof authenticates its full original metadata. -/
theorem Packet.after {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store}
    {initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    (packet : Packet owner caller _ initial)
    (reached : State headers keys ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    Packet owner caller _ reached := by
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have original := (initial.rows owner.position).authority.unmapped
    rw [(initial.rows owner.position).frame_eq] at original
    exact original
  have bound := (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨_unmapped, unchanged⟩ := frame owner.key.frameLocation unmapped bound
  exact ⟨packet.globals, packet.reference, packet.bundle,
    CallableIndexedOwnedLambdaViewHeads.carries_of_stable_read reached owner packet.carried (unchanged.trans read)⟩

/-- Prepending the actual lexical value shifts all original canonical slots
and the bundle together; the actual pool and history are the same witness. -/
theorem Packet.prepend {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    (packet : Packet owner caller _ initial) (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Packet owner caller ⟨(id, type) :: scope, mapping, world, heap, store, value :: canonical⟩ initial := by
  refine ⟨CallableIndexedOwnedCanonicalState.globals_prepend owner 1 packet.globals id type value, ?_, ?_, packet.carried⟩
  · have offset : ((id, type) :: scope).length + 1 + compiled.indexed.base.globals.length =
        scope.length + 1 + compiled.indexed.base.globals.length + 1 := by simp; omega
    rw [offset]
    exact packet.reference
  · simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using packet.bundle

/-- Removing that same lexical slot restores the original observations while
retaining the actual reached pool, history and complete record lists. -/
theorem Packet.restore {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    {initial : State headers keys ⟨(id, type) :: scope, mapping, world, heap, store, value :: canonical⟩}
    (packet : Packet owner caller _ initial) :
    Packet owner caller ⟨scope, mapping, world, heap, store, canonical⟩ initial := by
  refine ⟨CallableIndexedOwnedCanonicalState.globals_restore owner 1 packet.globals, ?_, ?_, packet.carried⟩
  · have offset : ((id, type) :: scope).length + 1 + compiled.indexed.base.globals.length =
        scope.length + 1 + compiled.indexed.base.globals.length + 1 := by simp; omega
    have reference := packet.reference
    rw [offset] at reference
    exact reference
  · have bundle := packet.bundle
    simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using bundle

/-- An existing actual transition is wrapped at the same returned pool; its
real administrative preservation supplies the additional observations. -/
theorem transition_of_reached {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store}
    (initial : (protocol (headers := headers) owner caller).State ⟨scope, mapping, world, heap, store, canonical⟩)
    (transition : ProtectedStateTransition.Transition (CallableIndexedOwnedFunctionState.protocol headers keys) initial.val
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    ProtectedStateTransition.Transition (protocol owner caller) initial
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩ := by
  obtain ⟨reached, related⟩ := transition
  exact ⟨⟨reached, initial.property.after owner caller reached frame⟩, related⟩

def administrativeTransport : ProtectedStateTransition.AdministrativeTransport (protocol (headers := headers) owner caller) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    let reached := (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).extend state.val maps worlds frame metadata
    ⟨reached, Packet.after owner caller state.property reached frame⟩
  related := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).related state.val maps worlds frame metadata
  records_eq := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).records_eq state.val maps worlds frame metadata

def bindings : ProtectedStateTransition.Bindings (protocol (headers := headers) owner caller) where
  prepend := fun state id type value => ⟨state.val, Packet.prepend owner caller state.property id type value⟩
  prepend_related := fun state _ _ _ => Relates.refl state.val
  prepend_records := fun _ _ _ _ => rfl
  restore := fun state => ⟨state.val, Packet.restore owner caller state.property⟩
  restore_related := fun state => Relates.refl state.val
  restore_records := fun _ => rfl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

/-- The genuine marked allocator's real reached pool and actual prepended
reference supply the new packet. Its complete record-producing post is kept. -/
def markedProducer : ProtectedStateTransition.MarkedAllocation.Producer
    (protocol (headers := headers) owner caller) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native => (CallableIndexedOwnedMarkedAllocation.producer headers keys model).Ready state.val location native
  complete := by
    intro allocationOwner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, transition⟩ :=
      (CallableIndexedOwnedMarkedAllocation.producer headers keys model).complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.val ready
    obtain ⟨reached, related⟩ := transition
    have retained : Packet owner caller ⟨request.scope, _, _, after, _, canonical⟩ reached :=
      Packet.after owner caller initial.property reached frame
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨reached, Packet.prepend owner caller retained request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩⟩

theorem readyAt_of_stableOwner {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (markedProducer (headers := headers) owner caller model).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.val read

section Formation
open CallableIndexedLambdaNestedRuntimeBodyMeaning
variable {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {rank : Nat} {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

include prefixZero complete globals slots sameSource in
/-- Formation is a genuine leaf of the same generic call grammar. Its input
packet is original static/read provenance, and its returned pool is actual. -/
theorem formation_preserves_at (size : Nat) (unique : NodeOccurrencesUnique source) :
    ProtectedStateTransition.PreservesAt (protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (fun scope id lowered => Nonempty (LambdaAt (values := .initial compiled.compatible.checked)
        headers caller registry faults rank source context evidence scope id lowered)) faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    related heaps locals agrees typed initial trace
  obtain ⟨head⟩ := certified
  have same := Option.some.inj (found.symm.trans head.found)
  subst node
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedLambdaViewHeads.formation_preserves head profile complete globals slots initial.val owner prefixZero
      (initial.property.observed owner caller) initial.property.carried initial.property.bundle
      related agrees typed heaps sameSource unique trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition_of_reached owner caller initial transition frame⟩

include prefixZero complete globals slots sameSource in
/-- Native leaf completion retains the actual pool and its full observations,
while the original reflected Source grade remains independent. -/
theorem formation_reflects_at (size : Nat) :
    ProtectedStateTransition.ReflectsAt (protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source
      (fun scope id lowered => Nonempty (LambdaAt (values := .initial compiled.compatible.checked)
        headers caller registry faults rank source context evidence scope id lowered)) faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    related heaps locals agrees typed initial completed
  obtain ⟨head⟩ := certified
  have same := Option.some.inj (found.symm.trans head.found)
  subst node
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedLambdaViewHeads.formation_reflects head profile complete globals slots initial.val owner prefixZero
      (initial.property.observed owner caller) initial.property.carried initial.property.bundle
      related agrees typed heaps sameSource completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, finalHeaps,
    maps, worlds, frame, metadata, transition_of_reached owner caller initial transition frame⟩

end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
/-! Genuine body Source receipts choose the finite readiness catalog at the
same compiler origin. Every site follows original Source typing and syntax;
expression and callee obligations remain strict child interfaces. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableRuntimeBodyOrigins CallableIndexedOwnedBodySourceOrigin
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (origin : StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
  (runtime : Dynamic.SourceRuntimeValid program origin.context origin.function.source)

/-- Each assignment fact comes from the independently typed Source parent. -/
theorem assignment_sites : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts origin.function.source origin.expressionSyntax)
    (SourceAssignmentHasType origin.function.source)
    (SourceBitNotAssignmentValid origin.function.source) origin.function.source where
  assignment := by
    intro context id expected node resolution operator rhs facts found form
    obtain ⟨mode, rest, _syntax, typing⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.assignment origin.body.unique
      (ProtectedStateImperativeTypedSourceSites.head typing) found form
  snapshot := by
    intro context id expected node resolution facts found form
    obtain ⟨mode, rest, _syntax, typing⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.bit_not origin.body.unique
      (ProtectedStateImperativeTypedSourceSites.head typing) found form

variable (bindings : Bindings callerProtocol) (wellFormed : ProgramWellFormed program)

/-- Genuine Source site judgments and actual admission define this origin's
readiness inputs. There is no arbitrary-state Source typing transport. -/
def inputs : CallableRuntimeBodyReadyInputs.Inputs callerProtocol (readiness bridge) bindings
    program (source_origin origin runtime) where
  facts := ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax
  headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts origin.function.source origin.expressionSyntax
  exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts origin.function.source
  loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts origin.function.source origin.expressionSyntax
  initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts origin.function.source origin.expressionSyntax
  assignmentFacts := SourceAssignmentHasType origin.function.source
  snapshotFacts := SourceBitNotAssignmentValid origin.function.source
  sites := ProtectedStateImperativeTypedSourceSites.sites program origin.function.evidence runtime.graph
  initializerSites := ProtectedStateImperativeInitializerSourceSites.sites
  assignmentSites := assignment_sites origin
  transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings origin.function.source
  snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge origin.function.evidence wellFormed
    (source_origin origin runtime).validity (fun _ valid => valid.2)
    (fun _ valid => (origin.runtimeOf valid.1).covers)

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol origin.layouts origin.frameLayout
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport callerProtocol) (budget : Nat)

include extension faithful observations producer acquire transport in
/-- Strict admitted expression children construct only the finite Source
prefixes and recipe producers used by the existing shared body fold. -/
theorem preserving_kits [FunctionCalls.FaultTokens faults]
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    CallableRuntimeBodyReadyInputs.PreservingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget := by
  have below : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size) :=
    fun context valid size bounded => expressions context valid size (Nat.le_of_lt bounded)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro context valid scope assignment operator rhs
    exact CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (registry := registry) (certificate := origin.certificates context) (administrative := origin.administrative) (faults := faults) bridge functions extension origin.function.evidence
      transport faithful observations origin.body.unique wellFormed valid.2 (origin.runtimeOf valid.1).covers budget (below context valid)
  · intro context valid scope assignment operator rhs
    exact CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_fault
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (registry := registry) (certificate := origin.certificates context) (administrative := origin.administrative) (faults := faults) bridge functions extension origin.function.evidence
      transport faithful observations origin.body.unique wellFormed valid.2 (origin.runtimeOf valid.1).covers budget (below context valid)
  · exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) (solved := origin.solved) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy
      (fun _ valid => (source_origin origin runtime).runtimeOf valid) below
  · exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy below

include extension faithful observations producer acquire transport in
/-- Native children retain their own strict budget. The same actual recipe
producers return independent Source grades and the original reached states. -/
theorem reflecting_kits [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions)
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    CallableRuntimeBodyReadyInputs.ReflectingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget := by
  refine ⟨?_, ?_, ?_⟩
  · intro context valid scope assignment operator rhs
    exact CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_reflection
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (registry := registry) (certificate := origin.certificates context) (administrative := origin.administrative) (faults := faults) bridge functions extension origin.function.evidence
      transport faithful observations origin.body.unique wellFormed valid.2 (origin.runtimeOf valid.1).covers budget functionTypes (expressions context valid)
  · exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) (solved := origin.solved) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy
      (fun _ valid => (source_origin origin runtime).runtimeOf valid) functionTypes expressions
  · exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax)
      (certificates := origin.certificates) (administrative := origin.administrative)
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active)
      (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (registry := registry) (faults := faults) bridge functions origin.definitions origin.registered extension
      origin.function.evidence faithful observations guard producer acquire transport bindings origin.body.unique wellFormed
      (source_origin origin runtime).validity (fun _ valid => valid.2) (fun _ valid => (origin.runtimeOf valid.1).covers)
      (source_origin origin runtime).extend budget origin.diagnosticPolicy functionTypes expressions

/-- Convert the genuine admission record beside the same actual child post. -/
theorem preserving_expressions
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size) :=
  fun context valid size bounded => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _
    (expressions context valid size bounded)

/-- The native converter retains its actual witness and independent Source
trace, including successful raw value typing at that same post. -/
theorem reflecting_expressions
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context origin.function.evidence origin.function.source (origin.certificates context) faults size)) :
    ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size) :=
  fun context valid size bounded => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _
    (expressions context valid size bounded)

/-- This concrete readiness already contains genuine raw value and heap
facts on success, and only authentic reached-row histories on fault. -/
theorem admitted_post {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome} {index : Index} {state : callerProtocol.State index}
    (post : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPost callerProtocol (readiness bridge)
      context type outcome state) :
    CallableIndexedOwnedSourceAdmission.PostAdmission bridge context type outcome state := by
  cases outcome with
  | fault _ =>
    refine ⟨post, ?_⟩
    intro value same
    cases same
  | value _ =>
    refine ⟨post.1.rows, ?_⟩
    intro value same
    cases same
    exact ⟨post.2, post.1.heap⟩

/-- The reverse child adapter returns the identical real post and relation. -/
theorem admitted_child_preserves {context : SourceSemantics.Context} {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt callerProtocol (readiness bridge)
      program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
      (source := origin.function.source) (context := context) (faults := faults) size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context origin.function.evidence origin.function.source (origin.certificates context) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrativeContext environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related, admitted_post bridge post⟩

/-- Native reflection retains its original completion and independent Source
trace while translating only the actual post's proof facets. -/
theorem admitted_child_reflects {context : SourceSemantics.Context} {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt callerProtocol (readiness bridge)
      program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
      (source := origin.function.source) (context := context) (faults := faults) size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context origin.function.evidence origin.function.source (origin.certificates context) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrativeContext environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees typed initial admitted evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related, admitted_post bridge post⟩

include extension faithful observations producer acquire transport in
/-- The shared Ready family supplies these exact smaller expression results;
the finite catalog producers are constructed internally from them. -/
theorem preserving_ready_kits [FunctionCalls.FaultTokens faults]
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.PreservingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget :=
  preserving_kits bridge origin runtime bindings wellFormed functions extension faithful observations guard producer acquire transport budget
    (fun context valid size bounded => admitted_child_preserves bridge origin runtime bindings wellFormed functions
      (expressions context valid size bounded))

include extension faithful observations producer acquire transport in
/-- The native family uses the same real child witness at its strict budget. -/
theorem reflecting_ready_kits [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions)
    (expressions : ∀ context, (source_origin origin runtime).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt callerProtocol (readiness bridge)
          program origin.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs bridge origin runtime bindings wellFormed).exprFacts (origin.certificates context)
          (source := origin.function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.ReflectingKits callerProtocol (readiness bridge) bindings program
      (source_origin origin runtime) functions guard (inputs bridge origin runtime bindings wellFormed) budget :=
  reflecting_kits bridge origin runtime bindings wellFormed functions extension faithful observations guard producer acquire transport budget functionTypes
    (fun context valid size bounded => admitted_child_reflects bridge origin runtime bindings wellFormed functions
      (expressions context valid size bounded))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
/-! Public match proofs use the exact Source signature catalog selected by the
successful compiler factory. Native definitions do not establish Source catalog
validity; the original well-formed Source program supplies that judgment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
open Frontend SourceInference

/-- The actual public catalog retains its original Source signature list. -/
theorem signatures (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.compatible.checked.signatures = compiled.sourceProgram.signatures := by
  obtain ⟨types, metadata, accepted⟩ :=
    CallableIndexedOwnedPublicCatalogClosedSources.compiled_catalog compiled
  exact SourceCoreCompatibleCatalog.prepare_signatures accepted

/-- Source program validity applies to that same selected catalog. -/
theorem well_formed (compiled : SourceCoreUnifiedCompilation.Compiled)
    (valid : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    SignatureCatalogWellFormed compiled.compatible.checked.signatures := by
  rw [signatures compiled]
  exact valid.signatures

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedFunctionFinishBounds
/-! Actual Source parameter typing closes direct function-body transfers.
Nested Source faults retain their original reason and emitted token. The
finish endpoints derive this control fact from the reached Source trace. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (ExecutesAt)
open RecursiveNamedCallBounds (BodyTrace)
universe u v

namespace CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt

/-- The complete typed body is checked at the actual parameter heap. -/
theorem control_no_escape {program : Program} {function : Dynamic.Closure}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {size : Nat} {control : Dynamic.ControlOutcome}
    (receipt : SourceReceipt program function context environment before)
    (wellFormed : ProgramWellFormed program)
    (trace : ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext control after) :
    control.NoEscapedControl := by
  obtain ⟨staticFinal, facts, typing, completes⟩ := receipt.bodyTyped
  cases trace with
  | control executed =>
    exact Dynamic.FunctionStatementsExecute.noEscapedControl wellFormed
      receipt.runtime receipt.covers receipt.locals receipt.heapTyped typing
      completes executed.sound
  | fault failed =>
    constructor <;> intro next equal <;> cases equal

end CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt

namespace CallableIndexedOwnedTypedFunctionFinishBounds

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {type : Ty} {flow code : Expr}
  {fellThrough escaped : Word}
  (tree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  (unique : NodeOccurrencesUnique function.source)
  {faults : FunctionCalls.FaultRep}

include tree projection unique in
theorem WithReady.preserves_at_emitted_with_source_receipt {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt
      program function context environment before)
    (wellFormed : ProgramWellFormed program)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when_with_transfers
    (functions := functions) (program := program) (tree := tree)
    (projection := projection) (unique := unique) protocol readiness condition facts
    emitted validity size meaning valid bodyFacts environments heaps locals
    agrees typed reference read unmapped initial gate ready
    (fun actualTrace => by
      have closed := receipt.control_no_escape wellFormed actualTrace
      exact ⟨fun next equal => False.elim (closed.1 next equal),
        fun next equal => False.elim (closed.2 next equal)⟩)
  exact trace

include tree projection unique in
theorem WithReady.reflects_at_emitted_with_source_receipt {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt
      program function context environment before)
    (wellFormed : ProgramWellFormed program)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers
    (functions := functions) (program := program) (tree := tree)
    (projection := projection) (unique := unique) protocol readiness condition facts
    emitted validity budget size within meaning valid bodyFacts environments heaps locals
    agrees typed reference read unmapped initial gate ready
    (fun actualTrace => by
      have closed := receipt.control_no_escape wellFormed actualTrace
      exact ⟨fun next equal => False.elim (closed.1 next equal),
        fun next equal => False.elim (closed.2 next equal)⟩)
  exact evaluated

end CallableIndexedOwnedTypedFunctionFinishBounds
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
/-! Genuine contextual diagnostic sources retain the selected specialization
and its actual substitution. These finite factory receipts change no compiler
or diagnostic preparation behavior. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
open Core Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- The full-key selector accepts exactly its one retained original row. -/
theorem selected_filter {plan : Plan} {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    plan.specializations.filter (fun actual => decide (actual.key = key)) = [row] := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · cases accepted
    assumption
  · cases accepted

theorem selected_key {plan : Plan} {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  have occurs : row ∈ plan.specializations.filter (fun actual => decide (actual.key = key)) := by
    rw [selected_filter accepted]
    exact List.mem_singleton_self _
  exact of_decide_eq_true (List.mem_filter.mp occurs).2

theorem selected_member_eq {plan : Plan} {key : Key} {row actual : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (member : actual ∈ plan.specializations) (same : actual.key = key) : actual = row := by
  have occurs : actual ∈ plan.specializations.filter (fun actual => decide (actual.key = key)) :=
    List.mem_filter.mpr ⟨member, by simp only [same, decide_true]⟩
  rw [selected_filter accepted] at occurs
  exact List.mem_singleton.mp occurs

private theorem exact_caller_source {plan : Plan} {binding : SourceCoreLocalEvidence.Binding}
    {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreLocalEvidence.exactCaller plan binding = .ok caller) :
    SourceCompilationPlan.exactSpecialization plan binding.caller = .ok caller ∧
      caller.function.typedBody = binding.source := by
  unfold SourceCoreLocalEvidence.exactCaller at accepted
  obtain ⟨row, made, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
  · rename_i same
    dsimp only at accepted
    split at accepted
    · simp only [pure, Except.pure] at accepted
      cases accepted
      exact ⟨mapError_ok made, Classical.not_not.mp same⟩
    · cases accepted

/-- One accepted local factory retains the exact selected Source and active
substitution, including the original authenticated instance and full key. -/
theorem contextual_source_at {program : CheckedProgram} {plan : Plan}
    {candidate : SourceCoreLocalEvidence.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {item : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok item) :
    ∃ row, SourceCompilationPlan.exactSpecialization plan item.caller.key = .ok row ∧
      item.source = row.function.typedBody.applySubstitution item.substitution ∧
      item.instance = candidate ∧ candidate.origin.source = row.function.typedBody ∧
      item.caller.key = candidate.origin.caller := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, made, accepted⟩ := bind_ok accepted
  have facts := exact_caller_source made
  split at accepted
  · cases accepted
  · obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
    dsimp only at accepted
    split at accepted
    · obtain ⟨pair, _, accepted⟩ := bind_ok accepted
      obtain ⟨active, inherited⟩ := pair
      dsimp only at accepted
      split at accepted
      · simp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨reference, _, accepted⟩ := bind_ok accepted
        split at accepted
        · cases accepted
        · obtain ⟨valid, _, accepted⟩ := bind_ok accepted
          cases accepted
          have key := selected_key facts.1
          exact ⟨caller, by simpa only [SourceCoreLocalEvidence.contextualCaller, key] using facts.1,
            rfl, rfl, facts.2.symm, key⟩
      · cases accepted
    · cases accepted

/-- Every authentic returned same-key context uses that same original row. -/
theorem context_source_at_key {program : CheckedProgram} {plan : Plan}
    {candidates : List SourceCoreLocalEvidence.Instance} {contexts : List SourceCoreLocalEvidence.Prepared}
    {key : Key} {row : SourceSpecialization.SpecializedFunction} {item : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok contexts)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (member : item ∈ contexts) (same : item.caller.key = key) :
    item.source = row.function.typedBody.applySubstitution item.substitution := by
  obtain ⟨candidate, parent, made⟩ := SourceCoreStageCodebook.prepareContexts_authentic accepted member
  obtain ⟨original, selected, view, _, _, _⟩ := contextual_source_at made
  rw [same, record] at selected
  cases selected
  exact view

/-- The diagnostic pass receives exactly these authentic contextual sources.
The original local catalog is retained separately from its later callable rewrite. -/
structure FactoryAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)) : Prop where
  actual : ∃ locals0 : SourceCoreLocalPolymorphism.Catalog, ∃ root remaining,
    prepared.plan.seedKeys = root :: remaining ∧
    SourceCoreStageCodebook.prepareContexts prepared.sourceProgram prepared.plan
      (locals0.bindings.flatMap (·.instances)) = .ok prepared.contexts ∧
    SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial checked) prepared.plan root
      (prepared.contexts.map (fun item => (item.caller.key, item.source))) = .ok diagnostics

theorem of_catalog {program : CheckedProgram} {plan : Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok prepared)
    (found : prepared.diagnostics = some diagnostics) : FactoryAt prepared diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals0, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, contextsMade, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    cases found
  · rename_i root remaining roots
    obtain ⟨actual, actualMade, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨⟨locals0, root, remaining, roots, mapError_ok contextsMade, mapError_ok actualMade⟩⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨⟨locals0, root, remaining, roots, mapError_ok contextsMade, mapError_ok actualMade⟩⟩

theorem of_automatic {program : CheckedProgram} {plan : Plan} {fuel : Nat}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked)}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (found : automatic.prepared.diagnostics = some diagnostics) : FactoryAt automatic.prepared diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog baseMade found

/-- Sealed compilation retains the same actual contextual source list and issuer. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics) :
    FactoryAt compiled.indexed.base diagnostics := by
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared] at found ⊢
  exact of_automatic compiled.compatiblePrepared found

def SourceView (original actual : TypedSource) : Prop :=
  actual = original ∨ ∃ active, actual = original.applySubstitution active

def QuerySourceViews (key : Key) (original : TypedSource) (sources : List (Key × TypedSource)) : Prop :=
  ∀ owner actual, (owner, actual) ∈ sources → owner = key → SourceView original actual

/-- Full-key singleton selection authenticates original rows and every returned
contextual row in the exact ordered source inventory. -/
theorem source_views_of_contexts {program : CheckedProgram} {plan : Plan}
    {candidates : List SourceCoreLocalEvidence.Instance} {contexts : List SourceCoreLocalEvidence.Prepared}
    {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok contexts)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    QuerySourceViews key row.function.typedBody
      (plan.specializations.map (fun actual => (actual.key, actual.function.typedBody)) ++
        contexts.map (fun item => (item.caller.key, item.source))) := by
  intro owner actual member same
  rcases List.mem_append.mp member with original | contextual
  · obtain ⟨selected, selectedMember, pair⟩ := List.mem_map.mp original
    cases pair
    have equal := selected_member_eq record selectedMember same
    subst selected
    exact Or.inl rfl
  · obtain ⟨item, itemMember, pair⟩ := List.mem_map.mp contextual
    cases pair
    exact Or.inr ⟨item.substitution, context_source_at_key accepted record itemMember same⟩

theorem FactoryAt.source_views {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {key : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan key = .ok row) :
    QuerySourceViews key row.function.typedBody
      (prepared.plan.specializations.map (fun actual => (actual.key, actual.function.typedBody)) ++
        prepared.contexts.map (fun item => (item.caller.key, item.source))) := by
  obtain ⟨locals0, root, remaining, _, contextsMade, _⟩ := factory.actual
  exact source_views_of_contexts contextsMade record

theorem substituted_span (active : TypeSystem.Substitution) (node : ExpressionNode) :
    (node.applySubstitution active).span = node.span := rfl

theorem substituted_index_iff (active : TypeSystem.Substitution) (node : ExpressionNode)
    (base key : ExpressionId) :
    (node.applySubstitution active).form = .index base key ↔ node.form = .index base key := by
  cases form : node.form <;> simp [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, form]

theorem substituted_local_iff (active : TypeSystem.Substitution) (node : ExpressionNode)
    (name : String) (binder : Resolved.LocalId) :
    (node.applySubstitution active).form = .reference name (.local binder) ↔
      node.form = .reference name (.local binder) := by
  cases form : node.form <;> simp [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, form]
  case reference reference resolution =>
    cases resolution <;> simp [ReferenceResolution.applySubstitution]

/-- An actual substituted member comes from that same original expression
occurrence. No uniqueness or type equality is inferred here. -/
theorem substituted_contains {original : TypedSource} {active : TypeSystem.Substitution}
    {id : ExpressionId} {node : ExpressionNode}
    (contains : SourceSemantics.ContainsExpression (original.applySubstitution active) id node) :
    ∃ before, SourceSemantics.ContainsExpression original id before ∧ node = before.applySubstitution active := by
  obtain ⟨retained, member, same⟩ := List.mem_map.mp contains.1
  cases retained with
  | expression before =>
    cases same
    exact ⟨before, ⟨member, contains.2⟩, rfl⟩
  | statement before => cases same

theorem SourceView.local_origin {original actual : TypedSource} (view : SourceView original actual)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression actual id node)
    (form : node.form = .reference name (.local binder)) :
    ∃ before, SourceSemantics.ContainsExpression original id before ∧
      before.form = .reference name (.local binder) ∧ node.span = before.span := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, contains, form, rfl⟩
  · subst actual
    obtain ⟨before, retained, same⟩ := substituted_contains contains
    subst node
    exact ⟨before, retained, (substituted_local_iff active before name binder).mp form, rfl⟩

theorem SourceView.index_origin {original actual : TypedSource} (view : SourceView original actual)
    {id : ExpressionId} {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression actual id node) (form : node.form = .index base key) :
    ∃ before, SourceSemantics.ContainsExpression original id before ∧
      before.form = .index base key ∧ node.span = before.span := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, contains, form, rfl⟩
  · subst actual
    obtain ⟨before, retained, same⟩ := substituted_contains contains
    subst node
    exact ⟨before, retained, (substituted_index_iff active before base key).mp form, rfl⟩

/-- An authentic substituted index cannot shadow a canonical local read at
the same unique occurrence. The loop's actual issuer is still required. -/
theorem SourceView.no_index_at_read {original actual : TypedSource} (view : SourceView original actual)
    (unique : SourceSemantics.NodeOccurrencesUnique original)
    {id : ExpressionId} {read node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {base key : ExpressionId}
    (readContains : SourceSemantics.ContainsExpression original id read)
    (readForm : read.form = .reference name (.local binder))
    (indexContains : SourceSemantics.ContainsExpression actual id node)
    (indexForm : node.form = .index base key) : False := by
  obtain ⟨before, retained, form, _⟩ := view.index_origin indexContains indexForm
  have same : before = read := Option.some.inj
    ((SourceSemantics.lookupExpression?_complete unique retained).symm.trans
      (SourceSemantics.lookupExpression?_complete unique readContains))
  subst before
  rw [readForm] at form
  cases form

theorem SourceView.index_span_at {original actual : TypedSource} (view : SourceView original actual)
    (unique : SourceSemantics.NodeOccurrencesUnique original)
    {id : ExpressionId} {before node : ExpressionNode} {base key : ExpressionId}
    (canonical : SourceSemantics.ContainsExpression original id before)
    (contains : SourceSemantics.ContainsExpression actual id node) (form : node.form = .index base key) :
    before.form = .index base key ∧ node.span = before.span := by
  obtain ⟨selected, retained, selectedForm, span⟩ := view.index_origin contains form
  have same : selected = before := Option.some.inj
    ((SourceSemantics.lookupExpression?_complete unique retained).symm.trans
      (SourceSemantics.lookupExpression?_complete unique canonical))
  subst selected
  exact ⟨selectedForm, span⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
/-! A genuine formation fixes the stronger captured-prefix receipt at its
producer. Generic ValueRep inversion keeps an existential caller prefix, so
local storage must retain this original receipt when it is needed later. The
formation copies the captured cells, so the receipt describes the formed
closure over its copies in the formed state. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
open CallableIndexedLambdaNestedRuntimeBodyMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled program} {rank : Nat}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope id lowered)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations 1 scope canonical owner.key.frameLocation)
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
    (some (CallableIndexedNamedGeneration.state caller.named)))
  (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
    compiled.indexed.layouts.definitions}
  (heaps : GenericHeap.HeapRepresents model mapping world heap store)

/-- The formation records of the head's actual formation: the copies of its
captured cells, the formed closure over them and the formed state. -/
abbrev FormedRecord :=
  Formed model
    (captures_for complete globals
      (CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals)
      related agrees typed)
    (actualCode head environment)
    (historyAt head
      (CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals)
      environment)
    heap store owner.key.frameLocation

include slots heaps in
/-- The actual formation of the head copies its captured cells. -/
theorem formation_exists :
    Nonempty (FormedRecord head complete globals initial owner prefixZero observed history bundle related agrees typed
      (model := model)) := by
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals
  let captured : Captures compiled.indexed mapping world scope environment actual :=
    captures_for complete globals entry related agrees typed
  have capturedGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    have capturedGlobals := capture_globals_for complete globals slots entry related agrees typed
    have frame : entry.catalog.authority.frameLocation = owner.key.frameLocation :=
      (initial.rows owner.position).frame_eq
    simpa only [frame] using capturedGlobals
  have reference : captured.canonical[(actualCode head environment).referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    have referenceEq : (actualCode head environment).referenceIndex =
        scope.length + 1 + compiled.indexed.base.globals.length := reference_index head
    rw [referenceEq]
    exact capturedGlobals.reference
  have read : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode
      compiled.indexed.ancestry.layout.frame (historyAt head entry environment).native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  exact CallableIndexedLambdaValues.formation captured (actualCode head environment)
    (historyAt head entry environment) head.snapshots (reference_index head) heaps reference read

variable (formedRecord : FormedRecord head complete globals initial owner prefixZero observed history bundle related
  agrees typed (model := model))

include slots heaps in
/-- The same actual formation captures, code, history and support create the
selected closure receipt for a formed record, over its copies in the formed
state. -/
def of_formation :
    let code := actualCode head environment
    CallableIndexedOwnedIndirectExpressionHeads.ClosureAt (headers := headers) (keys := keys)
      (registry := registry) (faults := faults)
      formedRecord.finalMap formedRecord.finalWorld formedRecord.closure
      (FunctionValues.sourceType formedRecord.closure)
      (value code formedRecord.embedding (initial.rows owner.position).authority.current formedRecord.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial owner prefixZero observed history bundle globals
  let captured : Captures compiled.indexed mapping world scope environment actual :=
    captures_for complete globals entry related agrees typed
  let code : Code compiled.indexed (formed head environment) scope captured.administrative := actualCode head environment
  let currentHistory : History code := historyAt head entry environment
  let support : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code := actualSupport head environment
  have origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code currentHistory support :=
    CallableIndexedOwnedFunctionValues.ActualSourceOrigin.of_nested head entry environment
  have capturedGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    have capturedGlobals := capture_globals_for complete globals slots entry related agrees typed
    have frame : entry.catalog.authority.frameLocation = owner.key.frameLocation :=
      (initial.rows owner.position).frame_eq
    simpa only [frame] using capturedGlobals
  have nativeTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formedRecord.represents heaps.runtime_hasTypes)
  exact {
    owner := owner
    scope := scope
    capturedActual := formedRecord.closureActual
    callerPrefix := 1
    captured := formedRecord.captures
    code := formedRecord.closureCode
    history := formedRecord.closureHistory
    support := support.recapture formedRecord.captured
    origin := origin.recapture formedRecord.captured
    globals := capturedGlobals.of_slots formedRecord.slots
    referenceIndex := reference_index head
    sourceView := rfl
    value_eq := rfl
    type_eq := rfl
    typed := nativeTyped }

include slots heaps in
/-- The prefix is fixed by the original producer, before any generic read. -/
theorem caller_prefix :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).callerPrefix = 1 := rfl

include slots heaps in
/-- Selection retains the immutable logical owner from actual formation. -/
theorem owner_eq :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).owner = owner := rfl

include slots heaps in
/-- The ranked body remains associated with the original full named principal. -/
theorem principal_eq :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).support.1 = caller := rfl

include slots heaps in
/-- The actual formation history retains its authentic original Source seed. -/
theorem source_seed :
    (of_formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed
      heaps formedRecord).history.metadata = CallableIndexedNamedGeneration.state caller.named := rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics
/-! The actual public compatible compiler retains the callable diagnostic
factory beside its cached codebook. These finite receipts recover its original
place table and allocator boundary; no stage or invocation law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {map : ε → δ}
    {output : α} (accepted : action.mapError map = .ok output) : action = .ok output := by
  cases action with
  | error => cases accepted
  | ok => cases accepted; rfl

/-- A genuine present callable context keeps the exact diagnostic preparation
and the same base place inventory in the sealed compatible result. -/
theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (present : base.callableContext = some native) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
      base.diagnostics = some diagnostics ∧ base.callableDiagnostics = some native.diagnostics ∧
      SourceCoreCallableFaultSites.prepare base.plan native.table diagnostics.program.rootTable diagnostics.nextReason =
        .ok native.diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted; cases present
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, issued, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases Option.some.inj present
      exact ⟨diagnostics, rfl, rfl, mapError_ok issued⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted; cases present

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (present : automatic.prepared.callableContext = some native) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked),
      automatic.prepared.diagnostics = some diagnostics ∧ automatic.prepared.callableDiagnostics = some native.diagnostics ∧
      SourceCoreCallableFaultSites.prepare automatic.prepared.plan native.table diagnostics.program.rootTable diagnostics.nextReason =
        .ok native.diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared present

/-- The public sealed preparation is the same actual diagnostic producer. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (present : compiled.indexed.base.callableContext = some native) :
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some diagnostics ∧
      compiled.indexed.base.callableDiagnostics = some native.diagnostics ∧
      SourceCoreCallableFaultSites.prepare compiled.indexed.base.plan native.table diagnostics.program.rootTable diagnostics.nextReason =
        .ok native.diagnostics := by
  have base := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  have own : compiled.compatible.prepared.callableContext = some native := by rwa [base] at present
  have accepted := of_automatic compiled.compatiblePrepared own
  rw [base]
  exact accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCallableDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
/-! Genuine whole-source identity ownership supplies the two static freshness
facts used by a lambda Site shell. Both conclusions keep the same source and
actual occurrence; native typing and runtime graph validity are not inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
open Core Frontend SourceInference

private def nodeBinders : Node → List TypedBinder
  | .expression node => match node.form with
      | .lambda parameters _ _ => parameters
      | _ => []
  | .statement node => match node.form with
      | .letDecl binder _ => [binder]
      | .forLoop initial _ post _ => (initial ++ post).filterMap fun
          | .letDecl binder _ => some binder
          | _ => none
      | .matchWith resolution => resolution.cases.flatMap fun arm =>
          SourceCoreDataPlaces.patternBinders arm.pattern
      | _ => []

private def nodeHiddenIds : Node → List Resolved.LocalId
  | .statement node => match node.form with
      | .matchWith resolution => [resolution.hiddenScrutinee]
      | _ => []
  | .expression _ => []

private theorem declared_binders (source : TypedSource) :
    SourceCoreDataPlaces.declaredBinders source = source.inputs ++ source.nodes.flatMap nodeBinders := by
  unfold SourceCoreDataPlaces.declaredBinders
  apply congrArg (fun selected : Node → List TypedBinder => source.inputs ++ source.nodes.flatMap selected)
  funext node
  cases node <;> rfl

private theorem instruction_ids (instructions : List MatchPatternInstruction) :
    (SourceCoreDataPlaces.instructionBinders instructions).map (·.id) =
      MatchPatternInstruction.binderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;>
      simp [SourceCoreDataPlaces.instructionBinders, MatchPatternInstruction.binderIds] at ih ⊢ <;>
      exact ih

private theorem pattern_ids (pattern : TypedMatchPattern) :
    (SourceCoreDataPlaces.patternBinders pattern).map (·.id) = pattern.binderIds := by
  cases resolution : pattern.resolution <;>
    simp only [SourceCoreDataPlaces.patternBinders, TypedMatchPattern.binderIds, resolution]
  all_goals try rfl
  all_goals exact instruction_ids _

private theorem for_ids (items : List ForItemForm) :
    ((items.filterMap fun | .letDecl binder _ => some binder | _ => none).map (·.id)) =
      items.flatMap ForItemForm.definedLocalIds := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item <;> simp [ForItemForm.definedLocalIds, ih]

private theorem node_inventory (node : Node) :
    ((nodeBinders node).map (·.id) ++ nodeHiddenIds node).Perm node.definedLocalIds := by
  cases node with
  | expression expression =>
    cases form : expression.form <;>
      simp only [nodeBinders, nodeHiddenIds, Node.definedLocalIds, form,
        ExpressionForm.definedLocalIds, List.map_nil, List.append_nil] <;>
      exact List.Perm.refl _
  | statement statement =>
    cases form : statement.form with
    | matchWith resolution =>
      simpa only [nodeBinders, nodeHiddenIds, Node.definedLocalIds,
        form, StatementForm.definedLocalIds, List.map_flatMap, pattern_ids] using
        List.perm_append_singleton resolution.hiddenScrutinee
          (resolution.cases.flatMap fun arm => arm.pattern.binderIds)
    | forLoop initial condition post body =>
      simp only [nodeBinders, nodeHiddenIds, Node.definedLocalIds,
        form, StatementForm.definedLocalIds, List.append_nil, for_ids, List.flatMap_append]
      exact List.Perm.refl _
    | _ =>
      simp only [nodeBinders, nodeHiddenIds, Node.definedLocalIds, form,
        StatementForm.definedLocalIds, List.map_nil, List.map_cons, List.append_nil] <;>
      exact List.Perm.refl _

private theorem nodes_inventory (nodes : List Node) :
    ((nodes.flatMap fun node => (nodeBinders node).map (·.id)) ++
      nodes.flatMap nodeHiddenIds).Perm (nodes.flatMap Node.definedLocalIds) := by
  induction nodes with
  | nil => exact List.Perm.refl _
  | cons node rest ih =>
    have reorder := (List.perm_append_comm_assoc
      (rest.flatMap fun node => (nodeBinders node).map (·.id))
      (nodeHiddenIds node) (rest.flatMap nodeHiddenIds)).append_left
        ((nodeBinders node).map (·.id))
    have assembled :
        (((nodeBinders node).map (·.id)) ++ (nodeHiddenIds node ++
          ((rest.flatMap fun node => (nodeBinders node).map (·.id)) ++
            rest.flatMap nodeHiddenIds))).Perm
          (node.definedLocalIds ++ rest.flatMap Node.definedLocalIds) := by
      simpa only [List.append_assoc] using (node_inventory node).append ih
    simpa only [List.flatMap_cons, List.append_assoc] using reorder.trans assembled

private theorem source_inventory (source : TypedSource) :
    (((SourceCoreDataPlaces.declaredBinders source).map (·.id)) ++
      source.nodes.flatMap nodeHiddenIds).Perm source.definedLocalIds := by
  have assembled := (nodes_inventory source.nodes).append_left (source.inputs.map (·.id))
  rw [declared_binders, List.map_append, List.map_flatMap]
  simpa only [TypedSource.definedLocalIds, List.append_assoc] using assembled

/-- The actual lambda parameters are disjoint from declaration inputs in the
same globally unique source inventory. -/
theorem lambda_parameter_not_input {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (ownership : LocalIdentityOwnership source)
    (contains : ContainsExpression source id node)
    (form : node.form = .lambda parameters result body)
    {binder : TypedBinder} (member : binder ∈ parameters) :
    binder.id ∉ source.inputs.map (·.id) := by
  have unique : source.definedLocalIds.Nodup := by
    simpa only [typedSourceDefinedLocalIds_eq_carrier] using ownership.unique
  have separates := (List.nodup_append.mp unique).2.2
  have defined : binder.id ∈ source.nodes.flatMap Node.definedLocalIds := by
    apply List.mem_flatMap.mpr
    refine ⟨.expression node, contains.1, ?_⟩
    simpa only [Node.definedLocalIds, form, ExpressionForm.definedLocalIds] using
      List.mem_map.mpr ⟨binder, member, rfl⟩
  intro input
  exact separates binder.id input binder.id defined rfl

/-- The compiler's input-kind test is false for every actual lambda parameter. -/
theorem lambda_parameter_kind {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId}
    (ownership : LocalIdentityOwnership source)
    (contains : ContainsExpression source id node)
    (form : node.form = .lambda parameters result body)
    {binder : TypedBinder} (member : binder ∈ parameters) :
    source.inputs.any (fun input => decide (input.id = binder.id)) = false := by
  apply List.any_eq_false.mpr
  intro input present same
  have sameId : input.id = binder.id := of_decide_eq_true same
  exact lambda_parameter_not_input ownership contains form member
    (List.mem_map.mpr ⟨input, present, sameId⟩)

/-- The same accepted parameter receipt transports ordinary kinds to the
lowered parameter vector; no alternate binder inventory is introduced. -/
theorem lowered_parameter_kinds
    {values : SourceCoreCompatibleValues.Context}
    {prepared : CallableIndexedLambdaValues.Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreBasic.Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : CallableIndexedLambdaValues.Code prepared function scope administrative viewRelation)
    {id : ExpressionId} {node : ExpressionNode}
    (ownership : LocalIdentityOwnership function.source)
    (contains : ContainsExpression function.source id node)
    (form : node.form = .lambda function.parameters function.resultType function.body) :
    ∀ binding ∈ code.receipt.loweredParameters,
      function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
  intro binding member
  apply lambda_parameter_kind ownership contains form
  rw [CallableIndexedLambdaEntryPrefix.parameters code]
  exact List.mem_map.mpr ⟨binding, member, rfl⟩

/-- The globally unique inventory separates actual match-hidden identities
from every ordinary declaration, including inputs and pattern binders. -/
theorem match_hidden_fresh {source : TypedSource}
    (ownership : LocalIdentityOwnership source) :
    GenericImperativeMatch.MatchHiddenFresh source := by
  have unique : source.definedLocalIds.Nodup := by
    simpa only [typedSourceDefinedLocalIds_eq_carrier] using ownership.unique
  have reordered := (source_inventory source).symm.nodup unique
  have separates := (List.nodup_append.mp reordered).2.2
  intro id node resolution found form declared
  have hidden : resolution.hiddenScrutinee ∈ source.nodes.flatMap nodeHiddenIds := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement node, (lookupStatement?_sound found).1, ?_⟩
    simp only [nodeHiddenIds, form, List.mem_singleton]
  exact separates resolution.hiddenScrutinee declared resolution.hiddenScrutinee hidden rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
/-! Actual captured slot references determine the complete administrative prefix,
including method rows. Ordinary Source headers remain a separate subset. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues RecursiveNamedCatalog
open RecursiveNamedLambdaFormationHeads CallableIndexedOwnedPhysicalGlobals
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {scope : SourceCoreLocalCell.Scope}

theorem entry_prefix_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    {context : Core.Context} {environment : Dynamic.Environment}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller) context := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ context)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    have bundle := entry.bundle
    rw [typed] at bundle
    simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append] using bundle
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature := List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      have found := allSlots slot signature selected
      have atType := tag found
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag entry.reference
      rw [globals] at atType
      have outside : ¬ scope.length + 1 + compiled.indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + compiled.indexed.base.globals.length - scope.length = compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType


def captures_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    Captures compiled.indexed mapping world scope environment actual := by
  let represented := environments_prefix related (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller) (entry_prefix_for allSlots globals entry related)
  let same : EnvironmentsAgree ξ (canonical.take (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length)) actual :=
    agrees_prefix agrees (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length)
  exact {
    administrative := nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller
    canonical := canonical.take (scope.length + (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller).length)
    actualContext := actualContext
    embedding := ξ
    represented := represented
    agrees := same
    respects := TypedLexicalWhile.environment_respects represented.runtime_hasTypes typed same
    typed := typed }


theorem capture_globals_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope
      (captures_for allSlots globals entry related agrees typed).canonical entry.catalog.authority.frameLocation := by
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope canonical
      entry.catalog.authority.frameLocation :=
    ⟨entry.catalog.globals, by simpa only [globals] using entry.reference⟩
  apply observed.take
  · intro header member
    have bound := slots header member
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega


theorem capture_slots_for
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (allSlots : Slots compiled 1 scope canonical)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world context scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    Slots compiled 1 scope (captures_for allSlots globals entry related agrees typed).canonical := by
  intro slot signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have within : scope.length + 1 + slot <
      scope.length + (nativePrefix (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) caller).length := by
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  change (canonical.take _)[_]? = _
  rw [List.getElem?_take, if_pos within]
  exact allSlots slot signature found

/-- The real parameter spine prepends local cells to the same captured suffix. -/
theorem append_locals {callerPrefix : Nat} {capturedScope parameterScope : SourceCoreLocalCell.Scope}
    {captured added : Environment}
    (slots : Slots compiled callerPrefix capturedScope captured)
    (length : added.length = parameterScope.length) :
    Slots compiled callerPrefix (parameterScope ++ capturedScope) (added ++ captured) := by
  intro slot signature found
  have outside : added.length ≤ (parameterScope ++ capturedScope).length + callerPrefix + slot := by
    simp only [List.length_append]
    omega
  rw [List.getElem?_append_right outside]
  have offset : (parameterScope ++ capturedScope).length + callerPrefix + slot - added.length =
      capturedScope.length + callerPrefix + slot := by
    simp only [List.length_append]
    omega
  rw [offset]
  exact slots slot signature found

/-- Actual frame installation and parameter allocation retain the complete cache
and the exact captured global references in the stronger caller state. -/
def of_closure_spine
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {mapping : LocationMap} {store : Store} {frameLocation : Location} {native : NativeFrame}
    (physical : Authority compiled mapping store)
    (frameRead : store.read? frameLocation = some
      (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (next : NativeFrame) {index : ProtectedStateTransition.Index}
    (frame : AdministrativePreserved mapping
      (store.set frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      index.mapping index.store)
    (pool : CallableIndexedOwnedFunctionState.State headers keys index)
    {capturedScope parameterScope : SourceCoreLocalCell.Scope} {captured added : Environment}
    (slots : Slots compiled 1 capturedScope captured)
    (length : added.length = parameterScope.length)
    (scopeEq : index.scope = parameterScope ++ capturedScope)
    (spine : index.canonical = added ++ captured) :
    (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index :=
  ⟨⟨pool, by rw [scopeEq, spine]; exact append_locals slots length⟩,
    (physical.install frameRead next).extend frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNestedCanonicalState
/-! The same actual caller carries its named Source seed, full physical slot
layout and installed cache through lexical scopes and real heap effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNestedCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedOwnedPhysicalGlobals
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)

abbrev Packet := CallableIndexedOwnedNestedCanonicalState.Packet (headers := headers) owner caller

def slotsProtocol : ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { _initial : (CallableIndexedOwnedNestedCanonicalState.protocol
    (headers := headers) owner caller).State index // Slots compiled 1 index.scope index.canonical }
  records := fun state => records state.val.val
  Relates := fun first last => Relates first.val.val last.val.val
  refl := fun state => Relates.refl state.val.val
  trans := fun first last => first.trans last

def protocol := CallableIndexedOwnedPhysicalState.protocol (slotsProtocol (headers := headers) owner caller)

def canonical {index : ProtectedStateTransition.Index}
    (state : (protocol (headers := headers) owner caller).State index) :
    (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index :=
  ⟨⟨state.base.val.val, state.base.property⟩, state.physical⟩

def of_canonical {index : ProtectedStateTransition.Index}
    (state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State index)
    (packet : Packet owner caller index state.base.val) :
    (protocol (headers := headers) owner caller).State index := ⟨⟨⟨state.base.val, packet⟩, state.base.property⟩, state.physical⟩

/-- Restoring the named packet uses the actual reached pool and preserved frame. -/
def after {index : ProtectedStateTransition.Index}
    (initial : (protocol (headers := headers) owner caller).State index)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (reached : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      (index.extend mapping world heap store))
    (frame : AdministrativePreserved index.mapping index.store mapping store) :
    (protocol (headers := headers) owner caller).State (index.extend mapping world heap store) :=
  of_canonical owner caller reached (initial.base.val.property.after owner caller reached.base.val frame)

private def slotsCaller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Slots compiled 1 index.scope index.canonical) (slotsProtocol (headers := headers) owner caller) where
  pool := fun state => state.val.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds frame _metadata related =>
    ⟨⟨⟨reached, initial.val.property.after owner caller reached frame⟩, initial.property⟩, rfl, related⟩

def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Slots compiled 1 index.scope index.canonical ∧ Authority compiled index.mapping index.store)
    (protocol (headers := headers) owner caller) := CallableIndexedOwnedPhysicalState.carrier (slotsCaller owner caller)

def bridge := (carrier (headers := headers) owner caller).forgetSlots

private def slotsAdministrative : ProtectedStateTransition.AdministrativeTransport
    (slotsProtocol (headers := headers) owner caller) where
  extend := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨(CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller).extend state.val maps worlds frame metadata,
      state.property⟩
  related := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller).related state.val maps worlds frame metadata
  records_eq := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller).records_eq state.val maps worlds frame metadata

def administrativeTransport : ProtectedStateTransition.AdministrativeTransport
    (protocol (headers := headers) owner caller) :=
  CallableIndexedOwnedPhysicalState.administrativeTransport (slotsAdministrative owner caller)

private def slotsBindings : ProtectedStateTransition.Bindings (slotsProtocol (headers := headers) owner caller) where
  prepend := fun state id type value =>
    ⟨(CallableIndexedOwnedNestedCanonicalState.bindings owner caller).prepend state.val id type value,
      state.property.prepend id type value⟩
  prepend_related := fun state id type value =>
    (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).prepend_related state.val id type value
  prepend_records := fun state id type value =>
    (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).prepend_records state.val id type value
  restore := fun state =>
    ⟨(CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore state.val, state.property.restore⟩
  restore_related := fun state => (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore_related state.val
  restore_records := fun state => (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore_records state.val

def bindings : ProtectedStateTransition.Bindings (protocol (headers := headers) owner caller) :=
  CallableIndexedOwnedPhysicalState.bindings (slotsBindings owner caller)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

private def slotsMarked : ProtectedStateTransition.MarkedAllocation.Producer
    (slotsProtocol (headers := headers) owner caller) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner caller model).Ready state.val location native
  complete := by
    intro allocationOwner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner caller model).complete
        allocation annotation same definitions registered environments agrees heaps reference read payloadAt cell allocated initial.val ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨final, initial.property.prepend request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩

def markedProducer : ProtectedStateTransition.MarkedAllocation.Producer
    (protocol (headers := headers) owner caller) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model :=
  CallableIndexedOwnedPhysicalState.markedProducer (slotsMarked owner caller model)

theorem readyAt_of_stableOwner {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (markedProducer (headers := headers) owner caller model).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.base.val.val read

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNestedCanonicalState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedDataHeadBounds
/-! The original constructor/member/index head preserves and reflects finite
execution with a fault policy selected only at its actual index header and
ordered Source prefixes. Each unavailable lookup keeps its real raw mapping
fields, Source runtime views, final store and caller transition. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedDataHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues RecursiveNamedCallBounds RecursiveNamedBoundedContracts
open ProtectedStateExpressionOperandTyping
open CompatibleExpressionCalls (Head CallHeads)
open RecursiveNamedDataExpressionHeadBounds (Certificate)
open RecursiveNamedDataExpressionHeadBounds.Stateful (constructor_preserves_after_sequence constructor_reflects_after_sequence)
open RecursiveNamedDataExpressionHeadBounds.Stateful.WithReady (SequencePreservesFor SequenceReflectsFor)

private theorem missing_excludes {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (missing : Dynamic.ValueIndexMissing values index) (selected : Dynamic.ValueAt values index value) : False := by
  induction missing with
  | nil => cases selected
  | tail rest ih => cases selected with | tail child => exact ih child

private theorem at_functional {values : List Dynamic.Value} {index : Nat} {first second : Dynamic.Value}
    (left : Dynamic.ValueAt values index first) (right : Dynamic.ValueAt values index second) : first = second := by
  induction left with
  | head => cases right; rfl
  | tail _ ih => cases right with | tail rest => exact ih rest

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (missing : IndexFaultPostContracts.MissingPolicies values source functions registry program context evidence reasonAt faults)

universe u v
variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop)

private theorem forget_reached {initial final : ProtectedStateTransition.Index}
    {first : protocol.State initial} {outcome : Dynamic.ExpressionOutcome}
    (post : ProtectedStateTransition.WithReady.Reached protocol ready outcome first final) :
    ProtectedStateTransition.Transition protocol first final := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

include transport extension faithful functionLeaves functionTypes unique missing in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.PreservesAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequencePreservesFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedDataExpressionSourceBounds.constructor_inv receipt.metadata form unique valid trace
    exact constructor_preserves_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry
      (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
      sourceTrace packed (by omega)

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    have raw := RecursiveNamedDataExpressionSourceBounds.member_inv metadata form unique trace
    cases raw with
    | value childTrace selected childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | failure childTrace childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | shape childTrace invalid childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rcases (RecursiveNamedDataExpressionSourceBounds.index_inv header.metadata form unique trace).split with ⟨reason, baseSize, rfl, failed, baseSmaller⟩ | ⟨baseSource, middle, baseSize, baseTrace, baseSmaller, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, keySize, rfl, failed, keySmaller⟩ | ⟨keySource, keySize, keyTrace, keySmaller, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.fault failed)
          cases represented with
          | fault matched =>
            obtain ⟨finalState, secondRelated, _⟩ := transition
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult, _sourceTrace, _post⟩ :=
              ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace.sound keyTrace.sound (reasonAt id)
                  (missing header keyFound form baseTrace.sound keyTrace.sound)
            obtain ⟨keyState, keyRelated, _⟩ := keyTransition
            obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup



include transport extension faithful functionLeaves functionTypes missing in
theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequenceReflectsFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete
    | caseRight childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    rw [member_rename layout] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation.sound (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation.sound
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace.sound sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation.sound (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed.sound),
            .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | fault matched =>
              obtain ⟨finalState, secondRelated, _⟩ := transition
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation.sound
                (LanguageResult.bind_failure layout.valueType keyEvaluation.sound (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace.sound failed.sound),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨keySourceSize, outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult, _sourceTrace, _post⟩ :=
                ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                  (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace.sound
                    (by cases trace with | value keyTrace => exact keyTrace.sound) (reasonAt id)
                  (missing header keyFound form baseTrace.sound
                    (by cases trace with | value keyTrace => exact keyTrace.sound))
              rw [rename_prefix] at keyEvaluation
              have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation.sound keyEvaluation.sound
                (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              obtain ⟨keyState, keyRelated, _⟩ := keyTransition
              obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
              cases trace with
              | value keyTrace =>
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace.sound keyTrace.sound),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩





end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedDataHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedAdmittedDataHeadBounds
/-! Constructor, member and index heads consume genuine Source typing at their
actual input. Index's exact successful base post supplies key admission; its
terminal helper retains the same Source heap. The returned full parent trace
establishes post admission at that same reached state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedAdmittedDataHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateExpressionOperandTyping
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {calls : CompatibleExpressionCalls.CallHeads} {reasonAt : ExpressionId → Word}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (missing : IndexFaultPostContracts.MissingPolicies values source functions registry program context evidence reasonAt faults)

include transport extension faithful functionLeaves functionTypes missing

/-- Genuine parent typing supplies the original operand row independently of
the constructor's generated payload vector and native child types. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate calls values source context reasonAt certificate)
      faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedReachedDataHeadBounds.Head.preserves_at functions extension faithful
      functionLeaves functionTypes program evidence unique missing callerProtocol transport
      (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.PreservesAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.preserves_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      (fun {ids types codes} same sequence {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout actualTyped state ready =>
        CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge state ready sequence unique
          (by simpa only [same] using operandTyped) env hp lc layout actualTyped (budget + 1)
          (fun n bound => meaning n (by omega)))
      environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- Native reflection keeps its independent whole Source grade and actual
terminal witness before Source preservation supplies success-only admission. -/
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate calls values source context reasonAt certificate)
      faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedReachedDataHeadBounds.Head.reflects_raw_at functions extension faithful
      functionLeaves functionTypes program evidence missing callerProtocol transport
      (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.ReflectsAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.reflects_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      (fun {ids types codes} same sequence {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout actualTyped state ready =>
        CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge state ready sequence unique
          (by simpa only [same] using operandTyped) env hp lc layout actualTyped (budget + 1)
          (fun n bound => meaning n (by omega)))
      environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped sized frame⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedAdmittedDataHeadBounds
end
