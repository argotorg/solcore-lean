import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInvocationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionInvocationLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)
open SelectedCompilationStageCoercionLiftBounds
open SelectedCompilationCoercionInvocationBounds (represented_arguments)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {sourceCaller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : SourceInference.CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation sourceCaller available
    scope node policy input coercion output call)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  (port : Port step context invocation.evidence stages)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def LiftBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationStageMethodInvocationLifting.LiftContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child)
      port.principal.cached.compilation port.sourceAt functions installed budget

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {source : Dynamic.Value} {value : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source source value call.signature.parameterType)
  (headerHeap : Dynamic.HeapWellTyped port.principal.sourceFunction.context before)
  (headerArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context before [source] port.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows pool)
  (certified : ∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
    port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts)


private theorem source_body
    (ledger : context.solvedRequirements = sourceCaller.function.solvedRequirements)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : StepOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      before coercion source outcome after) :
    ∃ bodySize, RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      bodySize port.principal.sourceBody port.principal.dictionary before [source] outcome after ∧
      bodySize < size := by
  cases trace with
  | value trace =>
    cases trace with
    | primitive absent _ => exact False.elim (absent _ _ port.selected)
    | method selected invoked =>
      obtain ⟨rfl, rfl⟩ := port.agrees _ _ selected
      exact ⟨_, .value invoked, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault trace =>
    cases trace with
    | requirement fault =>
      exact False.elim (CallableCoercionRequirementSafety.selected_safe ledger step.selectedMethod port.selected fault)
    | primitiveInput absent _ _ => exact False.elim (absent _ _ port.selected)
    | method selected failed =>
      obtain ⟨rfl, rfl⟩ := port.agrees _ _ selected
      exact ⟨_, .fault failed, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include ownerFrame physical slots heaps represented headerHeap headerArguments stable certified in
/-- The original selected conversion enters the actual installed method frame.
The result retains either its complete ordinary outcome or an earlier genuine
stage rejection, including the heap reached before rejection. -/
theorem lifts (budget : Nat)
    (bodyMeaning : LiftBodies (headers := headers) (receiving := receiving) step port owner functions budget)
    (ledger : context.solvedRequirements = sourceCaller.function.solvedRequirements)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : StepOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      before coercion source outcome after)
    (within : size ≤ budget) :
    StepLift (Program.ofChecked compiled.sourceProgram) stages invocation context before coercion source outcome after := by
  obtain ⟨bodySize, sourceTrace, strict⟩ := source_body step port ledger trace
  have parameters := represented_arguments step port functions represented
  obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_certificate
    port.principal.cached port.principal.dictionary functions owner pool ownerFrame
    physical heaps.runtime_hasTypes slots port.selected (by obtain ⟨facts, typed⟩ := certified; exact ⟨_, _, facts, typed⟩)
  have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
    rw [capture.canonical_eq]
    exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
  obtain ⟨environment, bound, finalContext, staged, result, reached, allocated, bodyTrace, matched, adapted⟩ :=
    SelectedCompilationStageMethodInvocationLifting.lifts_invocation
      port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner pool
      (capture.frame_eq.trans ownerFrame.symm) heaps physical capturedSlots budget port.staged
      (bodyMeaning pool capture.installed parameters headerHeap headerArguments stable port.staged)
      sourceTrace (Nat.le_of_lt (Nat.lt_of_lt_of_le strict within))
  exact ⟨result, reached,
    .coercionMethod port.selected port.sourceAt.frame.roots port.staged port.sourceAt.extended allocated bodyTrace matched,
    adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionInvocationLifting
