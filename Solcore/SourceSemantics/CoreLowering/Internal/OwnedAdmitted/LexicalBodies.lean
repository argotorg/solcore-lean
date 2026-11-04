import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeControl

/-!
# Admitted profile: lexical bodies

Body entries, lexical allocation and readiness, expression bounds and sequences, and lexical tree bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
/-! Genuine Source parameter receipts establish the exact actual body entry.
All-row stability follows authentic frame installation and the real parameter
prefix. Successful bodies retain deep Source typing at the same reached state;
faults retain that state and stable rows. No administrative transport or body
execution law is stored in an entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
universe u

/-- The full original Source body and dictionary remain independent of native
projections. All fields concern the actual parameter heap and environment. -/
structure SourceReceipt (program : Program) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop where
  runtime : Dynamic.SourceRuntimeValid program context function.source
  covers : function.evidence.Covers context
  heapTyped : Dynamic.HeapWellTyped context heap
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  bodyTyped : ∃ finalContext facts,
    StatementsHaveType function.source { returnType := function.resultType } context function.body finalContext facts ∧
    BodyCompletes function.resultType facts

namespace SourceReceipt

/-- Authentic named Source instantiation and the actual parameter allocation
supply admission before any Core type projection. -/
theorem of_named {program : Program} {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    {instantiation : DeclarationInstantiation} {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (wellFormed : ProgramWellFormed program) (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment reached)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments types) :
    SourceReceipt program function context environment reached := by
  obtain ⟨runtime, covers, heapTyped, locals, facts, finalContext, typing, completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_named_parameters extended allocated beforeTyped argumentsTyped
      wellFormed frame
  exact ⟨runtime, covers, heapTyped, locals, finalContext, facts, typing, completes⟩

/-- The original selected trait method and complete dictionary supply Source
admission; no top-level function Header is fabricated. -/
theorem of_method {program : Program} {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    {callerContext context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId} {types : List TypeSystem.Ty}
    {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (wellFormed : ProgramWellFormed program)
    (selected : Dynamic.OperatorMethodSelected program callerContext callerEvidence traitName methodName requirements body function.evidence)
    (frame : CallableCoercionMethodFrame.Frame body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment reached)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments types) :
    SourceReceipt program function context environment reached := by
  obtain ⟨runtime, covers, heapTyped, locals, facts, finalContext, typing, completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_selected_method_parameters extended allocated beforeTyped argumentsTyped
      wellFormed selected frame
  exact ⟨runtime, covers, heapTyped, locals, finalContext, facts, typing, completes⟩

/-- A genuine lambda occurrence supplies independent body typing at the exact
actual parameter context and allocation. -/
theorem of_lambda {program : Program} {function : Dynamic.Closure} {compiled : SourceCoreUnifiedCompilation.Compiled}
    {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world scope function.captured actual)
    (code : CallableIndexedLambdaValues.Code compiled.indexed function scope captured.administrative)
    (history : CallableIndexedLambdaValues.History code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store location current ghost)
    (frame : Dynamic.ClosureFrame program function)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types) :
    SourceReceipt program function inputs.context entry.entry.environment entry.entry.heap := by
  obtain ⟨runtime, covers, heapTyped, locals, finalContext, facts, typing, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.admission_at_parameters captured code history inputs functions entry
      frame beforeTyped argumentsTyped
  exact ⟨runtime, covers, heapTyped, locals, finalContext, facts, typing, completes⟩

/-- The actual Source body trace supplies successful value and heap typing.
The proof depends only on the original parameter receipt and program typing. -/
theorem after_body_values {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap}
    (receipt : SourceReceipt program function context environment before)
    (wellFormed : ProgramWellFormed program) {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after) :
    ∀ value, outcome = .value value →
      Dynamic.ValueHasType context after value function.resultType ∧ Dynamic.HeapWellTyped context after := by
  intro value same
  obtain ⟨finalContext, facts, typing, completes⟩ := receipt.bodyTyped
  cases trace with
  | returned executed =>
    cases same
    have preserved := Dynamic.FunctionStatementsExecute.preserved wellFormed receipt.runtime receipt.covers
      receipt.locals receipt.heapTyped typing completes executed.sound
    cases preserved.outcome_typed with
    | returned typed => exact ⟨typed, preserved.heap_typed⟩
  | unit unitType executed =>
    cases same
    have preserved := Dynamic.FunctionStatementsExecute.preserved wellFormed receipt.runtime receipt.covers
      receipt.locals receipt.heapTyped typing completes executed.sound
    exact ⟨unitType.symm ▸ Dynamic.ValueHasType.unit, preserved.heap_typed⟩
  | fault _ => cases same
  | escaped _ _ => cases same

end SourceReceipt

section ActualEntries
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

/-- This is the original complete reached body entry, paired only with genuine
Source admission and all-row stable histories at that same actual pool. -/
structure Entry where
  original : CallableRuntimeBodyOrigins.Stateful.Entry callerProtocol condition origin functions
  source : SourceReceipt program origin.function origin.context original.environment original.heap
  rows : StableRows (bridge.pool original.initial)

/-- Deep Source typing and all-row stability describe this exact actual input. -/
theorem Entry.admission (entry : Entry bridge (condition := condition) (origin := origin) (functions := functions)) :
    Admission bridge origin.context entry.original.initial :=
  ⟨entry.source.heapTyped, entry.rows⟩

/-- Stable hook installation updates every row in the physical cohort to the
real carried history; distinct frames keep their own original stable history. -/
theorem stable_rows_install {index : ProtectedStateTransition.Index}
    (first : State headers keys index) (stable : StableRows first) (selected : Fin keys.length)
    {next : NativeFrame} {nextGhost : GhostFrame} {metadata : Option MetadataState}
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost metadata) :
    StableRows (CallableIndexedOwnedFunctionState.install first selected (.stable carried)) := by
  intro row
  change ∃ metadata, Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    ((first.install selected (.stable carried)).rows row).authority.current
    ((first.install selected (.stable carried)).rows row).authority.ghost metadata
  have current := CallableIndexedAuthorityPool.Pool.install_current first selected row (.stable carried)
  have ghost := CallableIndexedAuthorityPool.Pool.install_ghost first selected row (.stable carried)
  simp only [current, ghost]
  split
  · exact ⟨metadata, carried⟩
  · exact stable row

/-- Real parameter effects preserve all-row stability after the authentic hook
install. The wrapper keeps the same original Entry and its actual pool. -/
def Entry.of_parameters
    (entry : CallableRuntimeBodyOrigins.Stateful.Entry callerProtocol condition origin functions)
    (source : SourceReceipt program origin.function origin.context entry.environment entry.heap)
    {index : ProtectedStateTransition.Index} (first : State headers keys index)
    (stable : StableRows first) (selected : Fin keys.length)
    {next : NativeFrame} {nextGhost : GhostFrame} {metadata : Option MetadataState}
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost metadata)
    (parameters : AdministrativePreserved index.mapping
      (index.store.set keys[selected.val].frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      entry.mapping entry.store) :
    Entry bridge (condition := condition) (origin := origin) (functions := functions) :=
  ⟨entry, source, StableRows.after_administrative
    (CallableIndexedOwnedFunctionState.install first selected (.stable carried)) (bridge.pool entry.initial)
    (stable_rows_install first stable selected carried) parameters⟩

/-- A lexical binder changes the Source context through its genuine static
extension. The actual reached State and all-row receipt remain unchanged. -/
theorem admission_of_binder {index : ProtectedStateTransition.Index}
    (initial : callerProtocol.State index) {context next : SourceSemantics.Context} {binder : TypedBinder}
    (extension : BinderExtends origin.function.source.owner context binder next)
    (admitted : Admission bridge context initial) : Admission bridge next initial :=
  ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extension).mp admitted.heap, admitted.rows⟩

/-- The same genuine body Source trace supplies successful post typing. Faults
retain the actual post and stable rows without a deep heap-typing claim. -/
theorem after_body (wellFormed : ProgramWellFormed program)
    (entry : Entry bridge (condition := condition) (origin := origin) (functions := functions))
    {after : Dynamic.Heap} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (reached : callerProtocol.State ⟨origin.scope, mapping, world, after, store, entry.original.canonical⟩)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context
      entry.original.environment entry.original.heap outcome after)
    (frame : AdministrativePreserved entry.original.mapping entry.original.store mapping store) :
    PostAdmission bridge origin.context origin.function.resultType outcome reached := by
  refine ⟨StableRows.after_administrative (bridge.pool entry.original.initial) (bridge.pool reached) entry.rows frame, ?_⟩
  exact entry.source.after_body_values wellFormed trace


/-- This pointwise body contract requires genuine Source admission at its actual
input. It records the same returned state, with typing only for success. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ (entry : Entry bridge (condition := condition) (origin := origin) (functions := functions))
      {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context
      entry.original.environment entry.original.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.original.actual entry.original.store (origin.code.rename entry.original.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.original.mapping finalMap ∧ WorldExtends entry.original.world finalWorld ∧
      AdministrativePreserved entry.original.mapping entry.original.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.original.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
        finalMap finalWorld origin.administrative program origin.function origin.context origin.scope
        entry.original.environment entry.original.heap after outcome ∧
      ∃ reached : callerProtocol.State ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.original.canonical⟩,
        callerProtocol.Relates entry.original.initial reached ∧
        PostAdmission bridge origin.context origin.function.resultType outcome reached

/-- Reflection preserves the measured native input and returns its independent
Source grade, together with admission of the same actual successful post. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ (entry : Entry bridge (condition := condition) (origin := origin) (functions := functions))
      {value : Value} {finalStore : Store},
    EvaluationSize size entry.original.actual entry.original.store (origin.code.rename entry.original.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context
        entry.original.environment entry.original.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.original.mapping finalMap ∧ WorldExtends entry.original.world finalWorld ∧
      AdministrativePreserved entry.original.mapping entry.original.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.original.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
        finalMap finalWorld origin.administrative program origin.function origin.context origin.scope
        entry.original.environment entry.original.heap after outcome ∧
      ∃ reached : callerProtocol.State ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.original.canonical⟩,
        callerProtocol.Relates entry.original.initial reached ∧
        PostAdmission bridge origin.context origin.function.resultType outcome reached

/-- Add the genuine successful-post receipt to an existing actual producer at
this typed entry. Every original semantic field and returned state is retained. -/
theorem PreservesAt.of_stateful (wellFormed : ProgramWellFormed program) {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.PreservesAt callerProtocol condition functions program origin size) :
    PreservesAt bridge (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ := meaning entry.original trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related, after_body bridge wellFormed entry reached trace frame⟩

/-- The reflected Source trace authenticates the successful post; no native
heap-typing inference or comparison of native and Source grades is used. -/
theorem ReflectsAt.of_stateful (wellFormed : ProgramWellFormed program) {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.ReflectsAt callerProtocol condition functions program origin size) :
    ReflectsAt bridge (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ := meaning entry.original completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related, after_body bridge wellFormed entry reached trace frame⟩

end ActualEntries
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
/-! Real Source allocation and the actual marked allocator post provide the
next lexical admission. The original raw value typing is independent of native
ValueRep. Every captured value, environment, heap, effect and state relation
comes from the existing producer unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion TypedLexicalControl
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Only the genuine Source allocation and raw optional value type establish
deep typing of the new heap. Actual administrative effects retain all rows. -/
theorem after_allocation {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {source : TypedSource} {context nextContext : SourceSemantics.Context} {binder : TypedBinder}
    {location : Dynamic.Location} {value : Option Dynamic.Value}
    (admitted : Admission bridge context first)
    (extended : BinderExtends source.owner context binder nextContext)
    (valueTyped : Dynamic.OptionalValueHasType context initial.heap value binder.scheme.body)
    (allocated : Dynamic.Heap.Allocates initial.heap binder.scheme.body value location reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge nextContext last :=
  ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp
      (Dynamic.HeapWellTyped.allocate admitted.heap valueTyped allocated),
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))

include definitions registered in
/-- The absent binder retains the actual producer state and complete capture,
then establishes admission for that same post in its genuine next Source context. -/
theorem allocate_absent {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures canonical (absentRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ reached : callerProtocol.State
          ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge nextContext reached := by
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related⟩ :=
    TypedLexicalControl.Stateful.allocate_absent (values := .initial compiled.compatible.checked)
      functions definitions registered callerProtocol producer mono extended ordinary projection allocation annotation same
      environments heaps locals agrees actualTyped reference read allocated initial ready
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
    nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related,
    after_allocation bridge initial reached admitted extended (.none _) allocated preservation⟩

include definitions registered in
/-- The actual successful initializer post supplies genuine raw value typing.
The existing initialized allocator produces the next state verbatim. -/
theorem allocate_initialized {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (valueTyped : Dynamic.ValueHasType context before sourceValue binder.scheme.body)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures (value :: canonical) (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType scope) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      ∃ reached : callerProtocol.State
          ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge nextContext reached := by
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related⟩ :=
    TypedLexicalControl.Stateful.allocate_initialized (values := .initial compiled.compatible.checked)
      functions definitions registered callerProtocol producer mono extended ordinary allocation annotation same represented
      environments heaps locals agrees actualTyped reference read allocated initial ready
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
    nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related,
    after_allocation bridge initial reached admitted extended (.some valueTyped) allocated preservation⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds
/-! Admitted expression children consume genuine deep Source heap typing and
all-row stability at their actual input. A value returns admission at the same
reached state; a fault retains that state and stable rows. The existing static
Calls/Tree support fold is reused without a new induction or transport law. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate) (faults : GenericExpressionMeaning.FaultRep)

def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

variable {bridge model context evidence source certificate faults}

/-- An already closed actual-state producer supplies its actual post. Real
Source preservation adds admission; no state or record list is reconstructed. -/
theorem PreservesAt.of_stateful {size : Nat}
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (meaning : ProtectedStateTransition.PreservesAt callerProtocol model program context evidence source certificate faults size) :
    PreservesAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  exact CallableIndexedOwnedSourceAdmission.preserves_at model initial admitted wellFormed runtime covers
    certified found sourceTyped environments heaps locals agrees typed meaning trace

/-- The native child retains its independently measured Source trace and the
same actual final witness when successful admission is added. -/
theorem ReflectsAt.of_stateful {size : Nat}
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (meaning : ProtectedStateTransition.ReflectsAt callerProtocol model program context evidence source certificate faults size) :
    ReflectsAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  exact CallableIndexedOwnedSourceAdmission.reflects_at model initial admitted wellFormed runtime covers
    certified found sourceTyped environments heaps locals agrees typed meaning completed

/-- The actual two-child outcome preserves order and multiplicity. -/
def pairOutcome (first : Dynamic.Value) : Dynamic.ExpressionOutcome → DataExpressionSequence.Outcome
  | .value second => .ok [first, second]
  | .fault reason => .error reason

/-- A successful first child feeds its exact reached state and fresh admission
into the next producer. A fault in that second child stops at its real post.
The production packing helper and the original raw Source types are retained. -/
theorem preserves_pair_after_value
    {scope : SourceCoreLocalCell.Scope} {firstId secondId : ExpressionId}
    {firstCode secondCode : SourceCoreBasic.LoweredExpr} {firstNode secondNode : ExpressionNode}
    {firstSize secondSize : Nat}
    (firstMeaning : PreservesAt bridge model context evidence source certificate faults firstSize)
    (secondMeaning : PreservesAt bridge model context evidence source certificate faults secondSize)
    (firstCertified : certificate scope firstId firstCode) (secondCertified : certificate scope secondId secondCode)
    (firstFound : source.lookupExpression? firstId = some firstNode)
    (secondFound : source.lookupExpression? secondId = some secondNode)
    (firstTyped : ExpressionHasType source context firstId firstNode.type)
    (secondTyped : ExpressionHasType source context secondId secondNode.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before middle after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {firstValue : Dynamic.Value} {secondOutcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (firstTrace : RecursiveNamedCallBounds.ExpressionOutcome program firstSize context evidence source environment
      before firstId (.value firstValue) middle)
    (secondTrace : RecursiveNamedCallBounds.ExpressionOutcome program secondSize context evidence source environment
      middle secondId secondOutcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments [firstCode, secondCode]).expression.rename ξ) value finalStore ∧
      DataExpressionSequence.Result model finalMap finalWorld [firstNode.type, secondNode.type]
        [firstCode, secondCode] faults (pairOutcome firstValue secondOutcome) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context secondNode.type secondOutcome reached := by
  obtain ⟨native, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
      firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
    firstMeaning firstCertified firstFound firstTyped environments heaps locals agrees typed initial admitted firstTrace
  cases represented with
  | @value sourceValue nativeValue payload =>
    obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      secondMeaning secondCertified secondFound secondTyped (environments.extend firstMaps firstWorlds)
        middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees nativeValue)
        (.cons (model.runtime_hasType payload) (typed.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
    rw [GenericExpressionMeaning.rename_prefix] at second
    cases represented with
    | @value nextSource nextNative nextPayload =>
      refine ⟨.inRight .word (.pair nativeValue nextNative), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        reached, callerProtocol.trans firstRelated related, post⟩
      · simpa [SourceCoreCalls.packArguments, DataExpressionSequence.pair_rename] using
          LocalSequence.pair_success firstCode.type secondCode.type first second
      · simpa [pairOutcome, DataPatternValues.packValues] using
          DataExpressionSequence.Result.values (codes := [firstCode, secondCode])
            (.cons (model.extend payload maps worlds) (.cons nextPayload .nil))
    | fault matched =>
      refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        reached, callerProtocol.trans firstRelated related, post⟩
      simpa [SourceCoreCalls.packArguments, DataExpressionSequence.pair_rename] using
        LocalSequence.pair_right_failure firstCode.type secondCode.type first second

section Tree
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {reasonAt : ExpressionId → Word} {solved : List SolvedRequirement}
  {fuel : Nat} {literals : GenericExpressionMeaning.Certificate}
  (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)

/-- The existing support fold specializes to admitted contracts. No static
Tree, Source, runtime or sequence induction is added. -/
theorem preserves_tree_at_with_literals (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults child)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults smaller) →
      PreservesAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
        (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults child) :
    PreservesAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  exact RecursiveNamedExpressionTreeBounds.fold_contract_at_with_literals calls
    (fun child certificate => PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults child)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within fragments heads

/-- The same fold gathers native child contracts with their independently
returned Source grades and actual admitted successful post witnesses. -/
theorem reflects_tree_at_with_literals (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults child)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults smaller) →
      ReflectsAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
        (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults child) :
    ReflectsAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  exact RecursiveNamedExpressionTreeBounds.fold_contract_at_with_literals calls
    (fun child certificate => ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults child)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within fragments heads
end Tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
/-! Genuine admission supplies lexical readiness at the actual reached state.
Allocation uses original Source receipts; restoration keeps that same heap and
native store. Expression adapters retain the full original child result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

def readiness : Readiness callerProtocol where
  Ready := fun context {_} state => Admission bridge context state
  FaultReady := fun {_} state => StableRows (bridge.pool state)
  ValueFacts := Dynamic.ValueHasType
  ready_fault := fun admitted => admitted.rows
  fault_after := fun first last rows frame =>
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) rows frame

/-- Binder facts transport the genuine Source heap context. Every restored
row is authenticated by its own real read in the retained native store. -/
theorem allocation_transfers (bindings : ProtectedStateTransition.Bindings callerProtocol)
    (source : TypedSource) :
    AllocationTransfers callerProtocol (readiness bridge) bindings source where
  absent := by
    intro initial reached first last context nextContext binder location admitted extended allocated frame
    exact CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge first last admitted
      extended (.none _) allocated frame
  initialized := by
    intro initial reached first last context nextContext binder location value admitted extended typed allocated frame
    exact CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge first last admitted
      extended (.some typed) allocated frame
  restore_ready := by
    intro index context nextContext binder type value extended state admitted
    exact ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr admitted.heap,
      StableRows.after_administrative (bridge.pool state) (bridge.pool (bindings.restore state))
        admitted.rows (.refl _ _)⟩
  restore_fault := by
    intro index binder type value state rows
    exact StableRows.after_administrative (bridge.pool state) (bridge.pool (bindings.restore state))
      rows (.refl _ _)

/-- The original successful post provides both raw value typing and admission
at its actual witness. Faults retain that witness's stable rows. -/
theorem expression_post {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome} {index : ProtectedStateTransition.Index}
    {state : callerProtocol.State index}
    (post : PostAdmission bridge context type outcome state) :
    ExpressionPost callerProtocol (readiness bridge) context type outcome state := by
  cases outcome with
  | fault _ => exact post.rows
  | value _ =>
    obtain ⟨typed, admitted⟩ := post.at_value
    exact ⟨admitted, typed⟩

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}

theorem preserves_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model
      context evidence source certificate faults size) :
    ExpressionPreservesAt callerProtocol (readiness bridge) program evidence model
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) certificate
      (source := source) (context := context) (faults := faults) size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees actualTyped initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, expression_post bridge post⟩

theorem reflects_at {size : Nat}
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model
      context evidence source certificate faults size) :
    ExpressionReflectsAt callerProtocol (readiness bridge) program evidence model
      (ProtectedStateLexicalSourceSites.ExpressionFacts source) certificate
      (source := source) (context := context) (faults := faults) size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees actualTyped initial admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, expression_post bridge post⟩
end Expressions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
/-! Ordered admitted children use the same readiness sequence proof. Authentic
Source typing applies only to actual list members. Successful children pass
their exact reached state and deep heap admission to the next child; faults
retain that state and every row's own stable history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- Extract the actual stored type from the genuine Source typing row.
Duplicates retain their own list membership; no off-list expression is typed. -/
theorem member_expression_typed {source : TypedSource} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types)
    (member : id ∈ ids) (found : source.lookupExpression? id = some node) :
    ExpressionHasType source context id node.type := by
  cases typing with
  | nil => simp at member
  | @cons _ expression expressions type types head tail =>
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨stored, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact sourceType ▸ head
    · exact member_expression_typed unique tail member found
termination_by ids.length

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
  {ids : List ExpressionId} {sourceTypes originalSourceTypes : List TypeSystem.Ty}

/-- A reflected or preserved sequence supplies deep admission only on success.
Every outcome keeps the genuine reached pool and all-row stable histories. -/
structure PostSequenceAdmission (outcome : Outcome) {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index) : Prop where
  rows : StableRows (bridge.pool reached)
  successful : ∀ values, outcome = .ok values → Admission bridge context reached

/-- The next real child receives this same successful post. -/
theorem PostSequenceAdmission.at_values {values : List Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostSequenceAdmission bridge (context := context) (.ok values) reached) : Admission bridge context reached :=
  post.successful values rfl

/-- An admitted Source producer supplies readiness for this actual child. -/
theorem preserves_child_at {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt callerProtocol
      (Admission bridge context) size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  have sourceTyped := member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted
      (ProtectedStateTransition.SequenceBridge.call_trace trace)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, ?_⟩
  intro value same
  cases same
  exact post.at_value.2

/-- Native reflection keeps its independent Source grade and actual post. -/
theorem reflects_child_at {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt callerProtocol
      (Admission bridge context) size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  have sourceTyped := member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted completed
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ProtectedStateTransition.SequenceBridge.source_trace trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, ?_⟩
  intro value same
  cases same
  exact post.at_value.2

variable {scope : SourceCoreLocalCell.Scope} {codes : List SourceCoreBasic.LoweredExpr}

theorem preserves_values_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids sources after) (bounded : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  exact
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_values_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => preserves_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded

theorem preserves_fault_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_fault_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => preserves_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame⟩

theorem reflects_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedDataExpressionSequence.TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostSequenceAdmission bridge (context := context) outcome reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, successful⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.reflects_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => reflects_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, successful⟩

theorem preserves_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : ProtectedDataExpressionSequence.TraceAt program size context evidence source environment before ids outcome after) (bounded : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostSequenceAdmission bridge (context := context) outcome reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, successful⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => preserves_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, successful⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
/-! Genuine Source typing and actual input admission instantiate a neutral
whole-sequence producer. Only the extra post-admission proof is forgotten;
the full result, effects and identical reached witness remain. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes originalSourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes codes)
  (unique : NodeOccurrencesUnique source)
  (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)

include admitted tree unique typing environments heaps locals agrees typed in
/-- Source uses the original inclusive sequence budget at this actual input. -/
theorem preserves (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      model context evidence source certificate faults size) :
    ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := sourceTypes)
      (codes := codes) (faults := faults) model initial budget := by
  intro size outcome after execution bounded
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.preserves_bounded bridge budget tree unique typing meaning
      environments heaps locals agrees typed initial admitted execution bounded
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩

include admitted tree unique typing environments heaps locals agrees typed in
/-- Native keeps its strict budget and independently graded Source trace. -/
theorem reflects (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      model context evidence source certificate faults size) :
    ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := sourceTypes)
      (codes := codes) (faults := faults) model initial budget := by
  intro size value finalStore completed bounded
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique typing meaning
      environments heaps locals agrees typed initial admitted completed bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
/-! The existing lexical Tree folds consume authentic Source syntax and
admission at actual inputs. Real child posts and allocations supply each next
input; lexical restoration retains the actual returned pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory
open GenericLexicalStatements (Tree Scope ValuesContext)
open CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : ExpressionId → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (bindings : Bindings callerProtocol)
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (unique : NodeOccurrencesUnique source)

include definitions registered producer bindings acquire unique in
theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context →
      BinderExtends source.owner context binder nextContext → validity nextContext)
    (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : ∀ child, child ≤ budget → ∀ context, validity context →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (expressions context) faults child)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code) :
    PreservesAtFor callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) condition
      (GenericLexicalStatements.Syntax source expressionSyntax)
      (validity := validity) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) functions program evidence
      size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted trace
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.preserves_at_for
    (protocol := callerProtocol) (condition := condition) (producer := producer)
    (stateBindings := bindings) (acquire := acquire)
    (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child within context childValid => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge
      _ (expressionMeaning child within context childValid))
    tree valid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted trace

include definitions registered producer bindings acquire unique in
theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context →
      BinderExtends source.owner context binder nextContext → validity nextContext)
    (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : ∀ child, child ≤ budget → ∀ context, validity context →
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (expressions context) faults child)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code) :
    ReflectsAtFor callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) condition
      (GenericLexicalStatements.Syntax source expressionSyntax)
      (validity := validity) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) functions program evidence
      size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted completed
  exact
    RecursiveNamedLexicalTreeBounds.Stateful.WithReady.reflects_at_for
      (protocol := callerProtocol) (condition := condition) (producer := producer)
      (stateBindings := bindings) (acquire := acquire)
      (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (facts := GenericLexicalStatements.Syntax source expressionSyntax)
      (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
      (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
      (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
      functions definitions registered program evidence validity extend budget size bounded
      (fun child within context childValid => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge
        _ (expressionMeaning child within context childValid))
      tree valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped
      initial conditioned admitted completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
end
