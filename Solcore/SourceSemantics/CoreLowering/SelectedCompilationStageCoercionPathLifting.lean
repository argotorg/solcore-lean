import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionInvocationLifting

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionPathLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)
open SelectedCompilationStageCoercionLiftBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def LiftBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      SelectedCompilationStageCoercionInvocationLifting.LiftBodies
        (headers := headers) (receiving := receiving) step port owner functions budget ∧ LiftBodies tail budget

private inductive PathChildren (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap) (step : SourceInference.CoercionStep)
    (steps : List SourceInference.CoercionStep) (input : Dynamic.Value) (size : Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | head {child reason after}
      (failed : StepOutcome program child context evidence before step input (.fault reason) after)
      (smaller : child < size) : PathChildren program context evidence before step steps input size (.fault reason) after
  | cons {headSize tailSize converted middle plain after}
      (head : StepOutcome program headSize context evidence before step input (.value converted) middle)
      (tail : PathOutcome program tailSize context evidence middle steps converted plain after)
      (headLess : headSize < size) (tailLess : tailSize < size) :
      PathChildren program context evidence before step steps input size plain after

private theorem path_children {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap} {step : SourceInference.CoercionStep}
    {steps : List SourceInference.CoercionStep} {input : Dynamic.Value} {size : Nat} {plain : Dynamic.ExpressionOutcome}
    (trace : PathOutcome program size context evidence before (step :: steps) input plain after) :
    PathChildren program context evidence before step steps input size plain after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | cons head tail =>
      exact .cons (.value head) (.value tail)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault failed =>
    cases failed with
    | head failed => exact .head (.fault failed) (SourceExecutionSize.child_lt_stepSize (by simp))
    | tail head failed =>
      exact .cons (.value head) (.fault failed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

variable {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List SourceInference.CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (ownerFrame : owner.key.frameLocation = 0)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  (pool : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix scope canonical)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  {sourceValue : Dynamic.Value} {nativeValue : Value}
  (represented : ValueRep compiled.compatible.checked receiving functions mapping world source sourceValue nativeValue input.type)
  (heapTyped : Dynamic.HeapWellTyped context before)
  (valueTyped : Dynamic.ValueHasType context before sourceValue source)
  (stable : StableRows pool)

include ownerFrame runtime ledger physical slots agrees heaps represented heapTyped valueTyped stable in
theorem lifts (budget : Nat)
    (bodyMeaning : LiftBodies (headers := headers) (receiving := receiving) owner functions chain budget)
    (preservation : ∀ grade, SelectedCompilationCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain grade)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PathOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence before steps sourceValue outcome after)
    (within : size ≤ budget) :
    PathLift (Program.ofChecked compiled.sourceProgram) stages invocation context before steps sourceValue outcome after := by
  induction chain generalizing mapping world before store sourceValue nativeValue size outcome after with
  | nil =>
    cases trace with
    | value evaluated => cases evaluated; exact ⟨_, _, .coercionsNil, .completed⟩
    | fault failed => cases failed
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
    have certified := (preservation 0).1.1
    obtain ⟨headerHeap, headerArguments⟩ :=
      SelectedCompilationCoercionInvocationBounds.source_arguments step port certified runtime heapTyped valueTyped
    have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
        sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
    cases path_children trace with
    | head failed smaller =>
      obtain ⟨staged, reached, head, adapted⟩ := SelectedCompilationStageCoercionInvocationLifting.lifts
        step port owner functions pool ownerFrame physical slots heaps inputRep headerHeap headerArguments stable
        certified budget bodyMeaning.1 ledger failed (Nat.le_trans (Nat.le_of_lt smaller) within)
      cases adapted with
      | completed => exact ⟨_, _, .coercionsFault head, .completed⟩
      | rejected origin call reason reached => exact ⟨_, _, .coercionsFault head, .rejected origin call reason _⟩
    | cons head tailTrace headLess tailLess =>
      obtain ⟨staged, reachedHeap, headTrace, adapted⟩ := SelectedCompilationStageCoercionInvocationLifting.lifts
        step port owner functions pool ownerFrame physical slots heaps inputRep headerHeap headerArguments stable
        certified budget bodyMeaning.1 ledger head (Nat.le_trans (Nat.le_of_lt headLess) within)
      cases adapted with
      | rejected origin call reason reached => exact ⟨_, _, .coercionsFault headTrace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨grade, sized⟩ := Staging.Recursive.Size.CoercionStep.of_trace headTrace
        obtain ⟨converted, middleStore, middleMap, middleWorld, _invoked, resultRep, middleHeaps,
            _maps, _worlds, frame, _metadata, ⟨reached, _related⟩, headPreserved⟩ :=
          SelectedCompilationCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame
            physical slots agrees heaps inputRep headerHeap headerArguments stable certified grade
            (preservation grade).1.2 ledger sized (Nat.le_refl _)
        cases resultRep with
        | value convertedRep =>
          have converted := SelectedCompilationCoercionInvocationBounds.result_at_value
            step port certified runtime (headPreserved _ rfl)
          have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
          have nextRep := convertedRep
          rw [← middleType] at nextRep
          obtain ⟨outcome, after, tailTrace, adapted⟩ := ih reached (physical.extend frame) middleHeaps nextRep
            converted.heap_typed converted.value_typed (StableRows.after_administrative pool reached stable frame)
            bodyMeaning.2 (fun grade => (preservation grade).2) tailTrace (Nat.le_trans (Nat.le_of_lt tailLess) within)
          exact ⟨outcome, after, .coercionsCons headTrace tailTrace, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionPathLifting
