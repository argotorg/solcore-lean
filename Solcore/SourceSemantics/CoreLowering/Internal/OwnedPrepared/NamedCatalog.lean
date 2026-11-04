import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LoopAndMatchBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds

/-!
# Prepared callables: named catalog

Catalog producers, named parameter receipts, expression runtime bounds and invocation admission.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogProducers
/-! Authentic finite catalog recipes consume only their actual smaller child
results. Source facts identify visited contexts; the existing loop and post
producers keep the exact reached pools and independent Source/native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogProducers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open TypedLexicalWhile (Scope ValuesContext)
open ProtectedStateImperativeCatalogReady
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  (validity : SourceSemantics.Context → Prop)
  (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
  (covers : ∀ context, validity context → evidence.Covers context)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (budget : Nat) (diagnosticPolicy : AssignmentDiagnosticPolicy)
  {solved : List SolvedRequirement}
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)

variable {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
  (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
  (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)

local notation "PreparedAP" => (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
local notation "PreparedUP" => (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)
local notation "PreparedHP" => (fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := invalidProjection) (missingDefault := missingDefault)
  (invalidUnary := fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) tree)
local notation "PreparedR" => ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
  (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
  (administrative := administrative) PreparedAP PreparedUP

/-- The same actual post Tree and its Plan tokens yield its structural receipt. -/
theorem post_receipt {context scope items type code}
    (tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    (payload : PreparedHP tree) : PreparedR type (TypedForHeader.Fallthrough type) context scope items code := by
  obtain ⟨plan, coupled, tokens⟩ := payload
  exact GenericForHeader.Structural.of_coupled coupled tokens

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded in
theorem preserving_loops
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    ProtectedStateImperativeCatalogPayload.PreservingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.PreservingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      PreparedHP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_loops_with_receipts (stateTransport := stateTransport) (unique := unique)
    bridge functions evidence guard validity budget PreparedR PreparedHP
    (CallableIndexedOwnedPostReceiptOperations.prefixat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) bridge functions evidence guard validity budget PreparedHP PreparedR (post_receipt diagnosticPolicy) (CallableIndexedOwnedHeaderReceiptOperations.prepared_PrefixAt (AP := PreparedAP) (UP := PreparedUP) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning))
    (CallableIndexedOwnedPostReceiptOperations.faultat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults) bridge functions evidence guard validity budget PreparedHP PreparedR (post_receipt diagnosticPolicy) (CallableIndexedOwnedHeaderReceiptOperations.prepared_FaultAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning assignments))
    meaning

include definitions registered producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded in
theorem reflecting_loops
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    ProtectedStateImperativeCatalogPayload.ReflectingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.ReflectingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      PreparedHP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_loops_with_receipts (stateTransport := stateTransport) (unique := unique)
    bridge functions evidence guard validity budget PreparedR PreparedHP
    (CallableIndexedOwnedPostReceiptOperations.reflectsat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults) bridge functions evidence guard validity budget PreparedHP PreparedR (post_receipt diagnosticPolicy) (CallableIndexedOwnedHeaderReceiptOperations.prepared_ReflectsAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered evidence guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget reflection assignments))
    reflection

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded runtimeOf in
theorem preserving_heads
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    PreservingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.PreservingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_heads_with_receipts
    bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf PreparedR
    (CallableIndexedOwnedHeaderReceiptOperations.prepared_PrefixAt (AP := PreparedAP) (UP := PreparedUP) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning)
    (CallableIndexedOwnedHeaderReceiptOperations.prepared_FaultAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning assignments)
    meaning

include definitions registered extension producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded runtimeOf in
theorem reflecting_heads
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    ReflectingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.ReflectingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_heads_with_receipts
    bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf PreparedR
    (CallableIndexedOwnedHeaderReceiptOperations.prepared_ReflectsAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered evidence guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget reflection assignments)
    reflection

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogProducers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
/-! An actual named hook and parameter allocation retain their complete input
without a body profile. Source admission and all installed rows concern that
same reached pool. The existing invocation cores receive only a strict body
child at this genuine receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open RecursiveNamedBoundedContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- Every field belongs to the actual hook and parameter producer. Independent
Source typing describes the argument heap before the real allocation. -/
structure Receipt
    {initial : ProtectedStateTransition.Index} (argumentsPool : State headers keys initial)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (arguments : List Dynamic.Value) where
  origin : Word
  index : Int
  metadata : MetadataState
  administrative : Core.Context
  actualContext : Core.Context
  actual : Environment
  embedding : Renaming
  frameLocation : Location
  physical : frameLocation = owner.key.frameLocation
  selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin
  history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (.state index) (.named origin) (some metadata)
  emitted : header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
    (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode
  body : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments initial.heap
    (initial.store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
    initial.mapping initial.world administrative actualContext actual embedding frameLocation (.state index) (.named origin)
  reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    body.mapping, body.world, body.heap, body.store, body.canonical⟩
  related : Relates argumentsPool reached
  stable : StableRows argumentsPool
  heapTyped : Dynamic.HeapWellTyped header.function.context initial.heap
  argumentsTyped : Dynamic.ValuesHaveTypes header.function.context initial.heap arguments header.types

section Observations
variable {functions owner}
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) functions owner argumentsPool header arguments)

/-- Source instantiation and allocation supply the complete actual body seed. -/
theorem Receipt.source (wellFormed : ProgramWellFormed program) :
    SourceReceipt program header.function header.context receipt.body.environment receipt.body.heap :=
  SourceReceipt.of_named wellFormed header.frame header.extended receipt.body.allocation
    receipt.heapTyped receipt.argumentsTyped

/-- The real hook authenticates the complete named Source history. -/
theorem Receipt.allowed :
    CallableIndexedOwnedNamedCanonicalEntries.condition functions owner header receipt.body :=
  CallableIndexedOwnedNamedCanonicalEntries.authorized functions owner header
    receipt.physical receipt.selected receipt.history receipt.emitted receipt.body

/-- The actual parameter catalog retains the original global slots. -/
theorem Receipt.global_slots :
    CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner (owner.key.capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) receipt.body.canonical :=
  receipt.body.catalog.globals

/-- The real named history supplies the actual marked-allocation gate. -/
theorem Receipt.stable_owner :
    CallableIndexedOwnedAllocationProducer.StableOwner keys receipt.frameLocation (.state receipt.index) :=
  CallableIndexedOwnedNamedCanonicalEntries.stable_owner functions owner header receipt.body receipt.allowed

/-- Hook installation and the original parameter effects retain every row at
the same reached pool, including repeated physical frame snapshots. -/
theorem Receipt.rows : StableRows receipt.reached := by
  have parameterFrame := Eq.mp (congrArg (fun location => AdministrativePreserved initial.mapping
    (initial.store.set location (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
    receipt.body.mapping receipt.body.store) receipt.physical) receipt.body.frame
  exact StableRows.after_administrative
    (CallableIndexedOwnedFunctionState.install argumentsPool owner.position (.stable receipt.history))
    receipt.reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install argumentsPool receipt.stable owner.position receipt.history)
    parameterFrame

/-- Real zero-prefix and global-count receipts produce the principal packet
beside this exact reached pool. -/
theorem Receipt.packet (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ receipt.reached :=
  CallableIndexedOwnedNamedCanonicalEntries.packet functions owner header receipt.body receipt.reached
    prefixZero globals receipt.allowed

/-- Only the principal proof is added to the unchanged reached State. -/
def Receipt.nested (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :=
  CallableIndexedOwnedNamedCanonicalEntries.wrap functions owner header receipt.body receipt.reached
    prefixZero globals receipt.allowed

theorem Receipt.nested_pool (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    (receipt.nested prefixZero globals).val = receipt.reached := rfl

/-- Deep Source typing and the actual installed rows establish readiness. -/
theorem Receipt.nested_admission (wellFormed : ProgramWellFormed program)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length) :
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header))
      header.context (receipt.nested prefixZero globals) :=
  ⟨(receipt.source wellFormed).heapTyped, receipt.rows⟩

end Observations

private def poolBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

section Results
variable {functions owner}
  {faults : FunctionCalls.FaultRep}
  {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) functions owner argumentsPool header arguments)

/-- The result names the actual Header and BodyState directly and keeps the
full exit, reached pool and successful Source admission. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore ∧
  FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld header.function.resultType header.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
  AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
  Dynamic.HeapMetadataExtend receipt.body.heap after ∧
  TypedMixedNamedBody.ReachedExit compiled.compatible.checked (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
    program header.function header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    receipt.body.environment receipt.body.heap after outcome ∧
  ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
    Relates receipt.reached reached ∧
    PostAdmission (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached

/-- The strict Source child is pointwise at this whole actual parameter input. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {outcome after},
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context
      receipt.body.environment receipt.body.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      ResultAt receipt (faults := faults) outcome after value finalStore finalMap finalWorld

/-- Reflection returns an independent Source grade at the same native input. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {value finalStore},
    EvaluationSize size receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        receipt.body.environment receipt.body.heap outcome after ∧
      ResultAt receipt (faults := faults) outcome after value finalStore finalMap finalWorld

/-- Forget only the retained exit and admission when entering the unchanged
low invocation result schema. -/
theorem PreservesAt.to_body {size : Nat} (meaning : PreservesAt receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.SourceBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, _exit, reached, related, _post⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, reached, related⟩

theorem ReflectsAt.to_body {size : Nat} (meaning : ReflectsAt receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.NativeBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated, represented, heaps, maps, worlds,
    frame, metadata, _exit, reached, related, _post⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, reached, related⟩

end Results

section BodyCallbacks
variable {functions owner}
  {faults : FunctionCalls.FaultRep}

/-- Parameter code and body continuation remain those of the original entry. -/
def SourceBodiesFor (header : CallableIndexedOwnedFunctionValues.Header compiled program) (budget : Nat) : Prop :=
  ∀ {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
  ∀ receipt : Receipt (registry := registry) functions owner argumentsPool header arguments,
    ContinuationAgreement receipt.actual
      (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
      (header.parameterCode.rename receipt.embedding) receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) →
    RecursiveNamedBoundedContracts.Below budget (PreservesAt receipt (faults := faults))

/-- The measured prefix and saved caller restoration accompany the same
parameter input before a strict native body child is requested. -/
def NativeBodiesFor (header : CallableIndexedOwnedFunctionValues.Header compiled program) (budget : Nat) : Prop :=
  ∀ {initial : ProtectedStateTransition.Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
  ∀ receipt : Receipt (registry := registry) functions owner argumentsPool header arguments,
  ∀ {prefixSize bodyStore value finalStore},
    EvaluationSize prefixSize receipt.actual
      (initial.store.set receipt.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state receipt.index)))
      (header.parameterCode.rename receipt.embedding) value bodyStore → prefixSize < budget →
    finalStore = bodyStore.set receipt.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (argumentsPool.rows owner.position).authority.current) →
    RecursiveNamedBoundedContracts.Below budget (ReflectsAt receipt (faults := faults))

end BodyCallbacks

section Invocations
variable {functions owner}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {faults : FunctionCalls.FaultRep}
  {callerPrefix : Nat} {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {environment : Dynamic.Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) context initial)
  {originalTypes : List TypeSystem.Ty} {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
  (wellFormed : ProgramWellFormed program)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
  (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)

include admitted wellFormed sourceRuntime covers locals argumentTypes application in
/-- Actual ordered Source arguments establish admission for the genuine
parameter input; only its strict body child is supplied. -/
theorem source_invocations (budget : Nat)
    (bodies : SourceBodiesFor (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation physical selected history emitted
    entry agreement parameterPool parameterRelated _allowed child strict outcome after trace
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact PreservesAt.to_body receipt (bodies receipt agreement child strict) trace

include admitted wellFormed sourceRuntime covers locals argumentTypes application in
/-- The native route uses the actual independently recovered Source argument
trace before selecting the same strict body input. -/
theorem native_invocations (budget : Nat)
    (bodies : NativeBodiesFor (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted prefixRun prefixWithin restored entry parameterPool parameterRelated _allowed child strict
    bodyValue bodyFinalStore completed
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact ReflectsAt.to_body receipt (bodies receipt prefixRun prefixWithin restored child strict) completed

end Invocations
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds
/-! Genuine named parameter receipts enter the original low call cores. The
same expression support fold supplies ordered strict children and runtime
literal leaves while retaining the caller's complete actual pool. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedExpressionHeads (Globals)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

section Heads
variable {certificate : GenericExpressionMeaning.Certificate}

include wellFormed sourceRuntime covers unique idsUnique sameLayouts owners in
/-- The authentic Source row selects actual ordered arguments and their real
parameter receipt before the strict body child is consumed. -/
theorem preserves_head (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedPreparedNamedParameterReceipts.source_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application budget (bodies header member)) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

include wellFormed sourceRuntime covers unique sameLayouts in
/-- Native arguments recover their independent Source trace at the actual
post before the genuine parameter and body continuations are selected. -/
theorem reflects_head (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedPreparedNamedParameterReceipts.native_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application budget (bodies header member)) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

end Heads

section Trees
variable {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

private abbrev calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate :=
  RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (some evidence) headers compilation source context

/-- The original compiler Tree keeps its genuine named call certificates. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (calls (headers := headers) (compilation := compilation)
    (source := source) (context := context) evidence) fuel (.initial compiled.compatible.checked) source context solved reasonAt

/-- Runtime literal certificates remain the original selected ledger leaves. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals
    (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
    (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
    (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts in
theorem preserves_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed sourceRuntime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) transport
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
      budget child childWithin children
    exact preserves_head functions owner caller evidence wellFormed sourceRuntime covers unique owners idsUnique sameLayouts
      budget child childWithin (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts in
theorem reflects_at_with_literals {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed sourceRuntime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) transport
      functions extension faithful observations functionTypes evidence unique missing wellFormed sourceRuntime covers
      (calls (headers := headers) (compilation := compilation) (source := source) (context := context) evidence)
      budget child childWithin children
    exact reflects_head functions owner caller evidence wellFormed sourceRuntime covers unique sameLayouts
      budget child childWithin (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique owners idsUnique
  uninitialized missing sameLayouts in
theorem preserves_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  preserves_at_with_literals functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique owners idsUnique sameLayouts uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtimeLedger unique faults)
    budget size within bodies

include transport extension faithful observations functionTypes wellFormed sourceRuntime covers unique
  uninitialized missing sameLayouts in
theorem reflects_at_runtime (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers →
      CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
        (headers := headers) (functions := functions) (owner := owner) (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (RuntimeTree (headers := headers) (compilation := compilation) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) (fuel := fuel) evidence) faults size :=
  reflects_at_with_literals functions extension faithful observations functionTypes owner caller transport evidence
    wellFormed sourceRuntime covers unique sameLayouts uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtimeLedger source faults)
    budget size within bodies

end Trees
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedInvocationAdmission
/-! The strong named parameter result supplies the exit and admission at the
actual completed body pool. The generic invocation core retains that same
witness through its sole caller restoration. This downstream adapter adds
caller admission using only the pure post helper. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedInvocationAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedParameterMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedBoundedContracts

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}

/-- The real lexical exit and post share the completed body's actual pool.
The lexical environment uses the whole parameter administrative suffix. -/
def exit_admission_extra : NamedInvocationFaultPostContracts.BodyExtra
    (headers := headers) (keys := keys) (functions := functions)
    (registry := registry) (header := header) :=
  fun {_locations} {_capturePrefix} {_arguments} {_before} {_initialStore}
    {_initialMap} {_initialWorld} {administrative} {_actualContext} {_actual}
    {_ξ} {_frameLocation} {_current} {_ghost}
    entry _parameterState outcome after _value finalMap finalWorld _bodyStore bodyState =>
    TypedMixedNamedBody.ReachedExit compiled.compatible.checked
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
      finalMap finalWorld
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      program header.function header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.environment entry.heap after outcome ∧
    PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState

/-- Caller admission concerns the original returned body pool, with its saved
caller cell and source spine restored. The body exit and post remain retained. -/
def restored_exit_admission_extra {initial : ProtectedStateTransition.Index}
    (saved : State headers keys initial) (callerContext : SourceSemantics.Context)
    (selected : Fin keys.length) : NamedInvocationFaultPostContracts.BodyExtra
      (headers := headers) (keys := keys) (functions := functions)
      (registry := registry) (header := header) :=
  fun {_locations} {_capturePrefix} {_arguments} {_before} {_initialStore}
    {_initialMap} {_initialWorld} {_administrative} {_actualContext} {_actual}
    {_ξ} {_frameLocation} {_current} {_ghost}
    entry parameterState outcome after value finalMap finalWorld bodyStore bodyState =>
    exit_admission_extra (functions := functions) (registry := registry) (header := header)
      entry parameterState outcome after value finalMap finalWorld bodyStore bodyState ∧
    PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      callerContext header.function.resultType outcome
      (CallableIndexedOwnedBodyRestoration.returned saved bodyState selected)

section Pointwise
variable {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {initial : ProtectedStateTransition.Index} {caller : State headers keys initial}
  {arguments : List Dynamic.Value} {faults : FunctionCalls.FaultRep}

/-- Consume the strong Source receipt once and retain its same body witness. -/
theorem source_body_with_extra_at_receipt
    (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments)
    {size : Nat}
    (meaning : CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt
      receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.SourceBodyAtWithExtra
      NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (faults := faults) receipt.body receipt.reached size := by
  intro outcome after trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, bodyState, related, post⟩ := meaning trace
  have bodyPost : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState := post
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, ⟨bodyState, related, exit, bodyPost⟩,
    NamedInvocationFaultPostContracts.trivial_of_result represented⟩

/-- The native input returns its independent Source grade and actual body pool. -/
theorem native_body_with_extra_at_receipt
    (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments)
    {size : Nat}
    (meaning : CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt
      receipt (faults := faults) size) :
    CallableIndexedOwnedInvocationBounds.NativeBodyAtWithExtra
      NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (faults := faults) receipt.body receipt.reached size := by
  intro value bodyStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated,
    represented, heaps, maps, worlds, frame, metadata, exit, bodyState, related, post⟩ :=
    meaning completed
  have bodyPost : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState := post
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    heaps, maps, worlds, frame, metadata, ⟨bodyState, related, exit, bodyPost⟩,
    NamedInvocationFaultPostContracts.trivial_of_result represented⟩

end Pointwise

section Continuations
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  {arguments : List Dynamic.Value} {faults : FunctionCalls.FaultRep}
  (condition : BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations)
    (capturePrefix := owner.key.capturePrefix) functions registry header)

/-- The actual hook and parameter callback construct one genuine receipt;
independent raw argument admission and saved rows belong to this caller. -/
theorem source_continuation_with_extra (budget : Nat)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedInvocationBounds.SourceContinuationWithExtra
      (post := NamedInvocationFaultPostContracts.Trivial)
      (extra := exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical selected history emitted entry agreement parameterState related _allowed child strict
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments :=
    { origin := origin, index := index, metadata := metadata,
      administrative := administrative, actualContext := actualContext, actual := actual,
      embedding := ξ, frameLocation := frameLocation, physical := physical,
      selected := selected, history := history, emitted := emitted, body := entry,
      reached := parameterState, related := related, stable := savedRows,
      heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  intro outcome after trace
  exact source_body_with_extra_at_receipt receipt
    (bodies receipt agreement child strict) trace

/-- Keep the original measured native prefix and its restoration equation.
No parameter action or saved-cell restoration is repeated. -/
theorem native_continuation_with_extra (budget : Nat)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget) :
    CallableIndexedOwnedInvocationBounds.NativeContinuationWithExtra
      (post := NamedInvocationFaultPostContracts.Trivial)
      (extra := exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    prefixSize bodyStore value finalStore physical selected history emitted prefixRun
    prefixWithin restored entry parameterState related _allowed child strict
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt
      (registry := registry) functions owner caller header arguments :=
    { origin := origin, index := index, metadata := metadata,
      administrative := administrative, actualContext := actualContext, actual := actual,
      embedding := ξ, frameLocation := frameLocation, physical := physical,
      selected := selected, history := history, emitted := emitted, body := entry,
      reached := parameterState, related := related, stable := savedRows,
      heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  intro bodyValue completedStore completed
  exact native_body_with_extra_at_receipt receipt
    (bodies receipt prefixRun prefixWithin restored child strict) completed

end Continuations

section Returned
variable {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
  {callerContext : SourceSemantics.Context}
  {post : NamedInvocationFaultPostContracts.BodyFaultPost}
  {sourceParent : Nat} {nativeBudget : Option Nat}
  {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
  {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}

/-- Extend only the fact inside the existing causal receipt. The original
restored frame authenticates every saved/reached row at that same returned pool. -/
theorem returned_at_with_admission
    (savedRows : StableRows caller)
    (supports : Dynamic.TypeContextSupports header.context callerContext)
    (receipt : NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      sourceParent nativeBudget owner caller arguments outcome after value finalMap finalWorld finalStore) :
    NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (restored_exit_admission_extra (functions := functions) (registry := registry)
        (header := header) caller callerContext owner.position)
      sourceParent nativeBudget owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, extra, restoredFrame⟩ := receipt
  have postAtBody : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      header.context header.function.resultType outcome bodyState := extra.2
  have postAtCaller := CallableIndexedOwnedBodyRestorationAdmission.restore_post
    caller bodyState owner.position savedRows postAtBody supports restoredFrame
  exact ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords,
    ⟨extra, postAtCaller⟩, restoredFrame⟩

/-- Faults add only the returned stable-row post; no context support or
successful raw value/deep heap typing is inferred. The original exit is retained. -/
theorem returned_fault_at_with_admission {reason : Dynamic.SemanticFault}
    (savedRows : StableRows caller)
    (receipt : NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      sourceParent nativeBudget owner caller arguments (.fault reason) after value finalMap finalWorld finalStore) :
    NamedInvocationFaultPostContracts.ReturnedAtWithExtra
      (header := header) (functions := functions) (registry := registry) post
      (restored_exit_admission_extra (functions := functions) (registry := registry)
        (header := header) caller callerContext owner.position)
      sourceParent nativeBudget owner caller arguments (.fault reason) after value finalMap finalWorld finalStore := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, extra, restoredFrame⟩ := receipt
  have postAtCaller : PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
      callerContext header.function.resultType (.fault reason)
      (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) :=
    CallableIndexedOwnedBodyRestorationAdmission.restore_fault_post
      caller bodyState owner.position savedRows restoredFrame
  exact ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords,
    ⟨extra, postAtCaller⟩, restoredFrame⟩

end Returned

section Invocations
variable {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store}

/-- The original invocation core consumes the strong body callback once.
Caller admission is added purely inside its same returned causal receipt. -/
theorem invocation_preserves_bounded_at_with_admission
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (callerContext : SourceSemantics.Context)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (supports : Dynamic.TypeContextSupports header.context callerContext)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAtWithExtra (header := header) (functions := functions)
        (registry := registry) NamedInvocationFaultPostContracts.Trivial
        (restored_exit_admission_extra (functions := functions) (registry := registry)
          (header := header) caller callerContext owner.position) size (none) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition, returned⟩ :=
    CallableIndexedOwnedInvocationBounds.invocation_preserves_bounded_at_with_extra
      (faults := faults) owner sameLayouts condition authorized budget caller
      _member capture represented heaps NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (source_continuation_with_extra owner caller condition budget
        savedRows heapTyped argumentsTyped bodies) trace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition,
    returned_at_with_admission savedRows supports returned⟩

/-- The original invocation core consumes the strong body callback once.
Caller admission is added purely inside its same returned causal receipt. -/
theorem invocation_reflects_bounded_at_with_admission
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (callerContext : SourceSemantics.Context)
    (savedRows : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (supports : Dynamic.TypeContextSupports header.context callerContext)
    (bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) (functions := functions) (owner := owner)
      (registry := registry) (faults := faults) header budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAtWithExtra (header := header) (functions := functions)
        (registry := registry) NamedInvocationFaultPostContracts.Trivial
        (restored_exit_admission_extra (functions := functions) (registry := registry)
          (header := header) caller callerContext owner.position) sourceSize (some size) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition, returned⟩ :=
    CallableIndexedOwnedInvocationBounds.invocation_reflects_bounded_at_with_extra
      (faults := faults) owner sameLayouts condition authorized budget caller
      _member capture represented heaps NamedInvocationFaultPostContracts.Trivial
      (exit_admission_extra (functions := functions) (registry := registry) (header := header))
      (native_continuation_with_extra owner caller condition budget
        savedRows heapTyped argumentsTyped bodies) completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
    finalHeaps, maps, worlds, frame, metadata, transition,
    returned_at_with_admission savedRows supports returned⟩

end Invocations
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedInvocationAdmission
end
