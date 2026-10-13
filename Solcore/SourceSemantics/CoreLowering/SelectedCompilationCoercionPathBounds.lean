import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInvocationBounds
import Solcore.SourceSemantics.Staging.RecursiveErasure

/-! Ordered conversions preserve the exact reached pool, heap and physical
cache between calls. Each method continuation receives the original strict
budget; path recursion only composes already justified single steps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

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

/-- Body continuations are supplied by the shared numerical induction. -/
def SourceBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      ((∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
          port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts) ∧
        SelectedCompilationCoercionInvocationBounds.SourceBodies (headers := headers) (receiving := receiving) step port owner functions faults budget) ∧
        SourceBodies tail budget

def NativeBodies {source target input steps output calls}
    (chain : Chain compiled project compilation caller available scope node policy context invocation stages
      source target input steps output calls) (budget : Nat) : Prop :=
  match chain with
  | .nil => True
  | .cons step port _ tail =>
      ((∃ facts, Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
          port.principal.sourceBody port.sourceAt.types port.sourceAt.context facts) ∧
        SelectedCompilationCoercionInvocationBounds.NativeBodies (headers := headers) (receiving := receiving) step port owner functions faults budget) ∧
        NativeBodies tail budget

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
theorem preserves (budget : Nat)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.CoercionPath (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before steps sourceValue outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs actual compilation.internalReason store (.inRight .word nativeValue)
        (calls.map (CallableCoercionSpine.Call.rename ξ)) result finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld target output.type faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved context before after value target := by
  induction chain generalizing mapping world before store sourceValue nativeValue size outcome after with
  | nil =>
      cases trace
      refine ⟨_, store, mapping, world, .nil, .value represented, heaps,
        LocationMap.Extends.refl _, WorldExtends.refl _, AdministrativePreserved.refl _ _,
        Dynamic.HeapMetadataExtend.refl _, ⟨pool, Relates.refl pool⟩, ?_⟩
      intro value same
      cases same
      exact ⟨valueTyped, heapTyped, Dynamic.HeapMetadataExtend.refl _⟩
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
      obtain ⟨headerHeap, headerArguments⟩ := SelectedCompilationCoercionInvocationBounds.source_arguments step port bodyMeaning.1.1 runtime heapTyped valueTyped
      have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
          sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
      cases trace with
      | coercionsCons head path =>
          obtain ⟨converted, middleStore, middleMap, middleWorld, invoked, resultRep, middleHeaps,
              maps, worlds, frame, metadata, ⟨reached, related⟩, headPreserved⟩ :=
            SelectedCompilationCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable bodyMeaning.1.1 budget bodyMeaning.1.2 ledger head
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
          cases resultRep with
          | value convertedRep =>
              have converted := SelectedCompilationCoercionInvocationBounds.result_at_value
                step port bodyMeaning.1.1 runtime (headPreserved _ rfl)
              have convertedTyped := converted.value_typed
              have middleTyped := converted.heap_typed
              have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
              have nextRep := convertedRep
              rw [← middleType] at nextRep
              obtain ⟨result, finalStore, finalMap, finalWorld, remaining, resultRep, finalHeaps,
                  tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨returned, tailRelated⟩, tailPreserved⟩ :=
                ih reached (physical.extend frame) middleHeaps nextRep middleTyped convertedTyped
                  (StableRows.after_administrative pool reached stable frame) bodyMeaning.2 path
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              refine ⟨result, finalStore, finalMap, finalWorld, .cons invoked remaining,
                resultRep, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
                frame.trans tailFrame, metadata.trans tailMetadata, ⟨returned, related.trans tailRelated⟩, ?_⟩
              intro value same
              have preserved := tailPreserved value same
              exact ⟨preserved.value_typed, preserved.heap_typed, metadata.trans preserved.heap_extends⟩
      | coercionsFault head =>
          obtain ⟨converted, finalStore, finalMap, finalWorld, invoked, resultRep, finalHeaps,
              maps, worlds, frame, metadata, ⟨reached, related⟩, headPreserved⟩ :=
            SelectedCompilationCoercionInvocationBounds.preserves step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable bodyMeaning.1.1 budget bodyMeaning.1.2 ledger head
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
          cases resultRep with
          | fault matched =>
              have finalType : CallableCoercionSpine.finalType call.signature.resultType
                  (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
                simpa only [step.emitted] using tail.final_type ξ
              refine ⟨_, finalStore, finalMap, finalWorld, .cons invoked ?_, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, ⟨reached, related⟩, ?_⟩
              · simpa only [finalType] using CallableCoercionSpine.Runs.failure actual compilation.internalReason
                  finalStore call.signature.resultType _ (calls.map (CallableCoercionSpine.Call.rename ξ))
              · intro value same
                cases same

private theorem failed_runs {budget : Nat} {environment : Environment} {reason : Word}
    {store finalStore : Store} {tag : Ty} {payload result : Value} {calls : List CallableCoercionSpine.Call}
    (trace : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget environment reason)
      store (.inLeft tag payload) calls result finalStore) :
    result = .inLeft (CallableCoercionSpine.finalType tag calls) payload ∧ finalStore = store := by
  generalize original : Value.inLeft tag payload = input at trace
  induction trace generalizing tag with
  | nil => cases original; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      cases original
      cases head with
      | skipped => exact ih rfl

include ownerFrame runtime physical slots agrees heaps represented heapTyped valueTyped stable in
theorem reflects (budget : Nat)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {result : Value} {finalStore : Store}
    (completed : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget actual compilation.internalReason)
      store (.inRight .word nativeValue) (calls.map (CallableCoercionSpine.Call.rename ξ)) result finalStore) :
    ∃ size outcome after finalMap finalWorld,
      Staging.Recursive.Size.CoercionPath (Program.ofChecked compiled.sourceProgram) stages size
        invocation context before steps sourceValue outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld target output.type faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) pool
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ value, outcome = .value value →
        Dynamic.ExpressionEvaluationPreserved context before after value target := by
  induction chain generalizing mapping world before store sourceValue nativeValue result finalStore with
  | nil =>
      cases completed
      refine ⟨_, .value sourceValue, before, mapping, world, .coercionsNil, .value represented, heaps,
        LocationMap.Extends.refl _, WorldExtends.refl _, AdministrativePreserved.refl _ _,
        Dynamic.HeapMetadataExtend.refl _, ⟨pool, Relates.refl pool⟩, ?_⟩
      intro value same
      cases same
      exact ⟨valueTyped, heapTyped, Dynamic.HeapMetadataExtend.refl _⟩
  | @cons coercion target input middle output rest call calls step port valid tail ih =>
      obtain ⟨headerHeap, headerArguments⟩ := SelectedCompilationCoercionInvocationBounds.source_arguments
        step port bodyMeaning.1.1 runtime heapTyped valueTyped
      have inputRep : ValueRep compiled.compatible.checked receiving functions mapping world coercion.source
          sourceValue nativeValue call.signature.parameterType := step.inputType.symm ▸ represented
      cases completed with
      | cons head remaining =>
          obtain ⟨sourceSize, outcome, middleHeap, middleMap, middleWorld, trace, resultRep, middleHeaps,
              maps, worlds, frame, metadata, ⟨reached, related⟩, headPreserved⟩ :=
            SelectedCompilationCoercionInvocationBounds.reflects
              step port owner functions faults pool ownerFrame physical slots agrees heaps
              inputRep headerHeap headerArguments stable bodyMeaning.1.1 budget bodyMeaning.1.2 head
          cases resultRep with
          | value convertedRep =>
              have converted := SelectedCompilationCoercionInvocationBounds.result_at_value
                step port bodyMeaning.1.1 runtime (headPreserved _ rfl)
              have convertedTyped := converted.value_typed
              have middleTyped := converted.heap_typed
              have middleType : middle.type = call.signature.resultType := by rw [step.emitted]
              have nextRep := convertedRep
              rw [← middleType] at nextRep
              obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, finalRep, finalHeaps,
                  tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨returned, tailRelated⟩, tailPreserved⟩ :=
                ih reached (physical.extend frame) middleHeaps nextRep middleTyped convertedTyped
                  (StableRows.after_administrative pool reached stable frame) bodyMeaning.2 remaining
              refine ⟨_, outcome, after, finalMap, finalWorld, .coercionsCons trace tailTrace,
                finalRep, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
                frame.trans tailFrame, metadata.trans tailMetadata, ⟨returned, related.trans tailRelated⟩, ?_⟩
              intro value same
              have preserved := tailPreserved value same
              exact ⟨preserved.value_typed, preserved.heap_typed, metadata.trans preserved.heap_extends⟩
          | fault matched =>
              have finalType : CallableCoercionSpine.finalType call.signature.resultType
                  (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
                simpa only [step.emitted] using tail.final_type ξ
              obtain ⟨sameResult, rfl⟩ := failed_runs remaining
              rw [finalType] at sameResult
              subst result
              refine ⟨_, _, middleHeap, middleMap, middleWorld, .coercionsFault trace, .fault matched,
                middleHeaps, maps, worlds, frame, metadata, ⟨reached, related⟩, ?_⟩
              intro value same
              cases same

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds
