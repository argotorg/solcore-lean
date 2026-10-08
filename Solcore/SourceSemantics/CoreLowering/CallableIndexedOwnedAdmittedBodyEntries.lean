import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins

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
