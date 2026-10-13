import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercedExpressionSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalRawDirectBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds

/-! Original direct-call forms and their authentic ordered conversions compose
at the same reached physical state. Both internal body continuations use one
budget; the original staged trace supplies the final Source admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedDirectExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open SelectedCompilationPhysicalRawDirectBounds (RawPreservesAt RawReflectsAt)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {lowerChild : SourceCoreEvidence.Child} {fuel : Nat} {callables : SourceCoreFunctions.CallablePolicy}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    lowerChild fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (ownerFrame : owner.key.frameLocation = 0)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)
  {stages : Staging.Recursive.Registry} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller receipt.available scope node callables context invocation stages
    node.rawType node.type receipt.operand node.coercions output calls)
  (nonempty : node.coercions ≠ [])
  (unique : NodeOccurrencesUnique invocation.source)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (typed : ExpressionHasType invocation.source context id node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
    environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission callerBridge.forgetSlots context initial)

include physical slots ownerFrame chain nonempty unique runtime ledger typed environments heaps locals agrees actualTyped admitted in
theorem preserves (budget : Nat)
    (rawMeaning : ∀ size, size ≤ budget → RawPreservesAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : SelectedCompilationCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission callerBridge.forgetSlots context node.type outcome reached := by
  rcases CallableIndexedOwnedPreparedStagedCoercedExpressionSource.branches receipt.found unique nonempty trace with
    ⟨rawSize, pathSize, source, middle, sameSize, rawTrace, pathTrace⟩ |
    ⟨rawSize, failure, sameSize, outcomeEq, rawTrace⟩
  · have rawLess : rawSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have pathLess : pathSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have rawWithin : rawSize ≤ budget := Nat.le_trans (Nat.le_of_lt rawLess) within
    have pathWithin : pathSize ≤ budget := Nat.le_trans (Nat.le_of_lt pathLess) within
    obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
        maps, worlds, frame, metadata, middleState, related, rawPost⟩ :=
      rawMeaning rawSize rawWithin typed environments heaps locals agrees actualTyped initial admitted rawTrace
    cases represented with
    | value valueRep =>
      have valueTyped := rawPost.at_value.1
      have middleTyped := rawPost.at_value.2.heap
      obtain ⟨value, finalStore, finalMap, finalWorld, runs, result, finalHeaps,
          tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨finalPool, tailRelated⟩, preserved⟩ :=
        SelectedCompilationCoercionPathBounds.preserves owner functions faults chain ownerFrame
          runtime ledger (callerBridge.pool middleState) (physical middleState) (slots middleState)
          agrees middleHeaps valueRep middleTyped valueTyped
          (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
            (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
          budget bodyMeaning pathTrace pathWithin
      obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore middleState finalPool
        tailMaps tailWorlds tailFrame tailMetadata tailRelated
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, result, finalHeaps,
        maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame, metadata.trans tailMetadata,
        returned, callerProtocol.trans related returnedRelated, ?_⟩
      · exact (chain.spine.renamed_completed_iff ξ).mpr ⟨_, _, evaluated, runs⟩
      · exact after_expression_sized_of_preserved initial returned admitted trace (fun value same => ⟨(preserved value same).value_typed, (preserved value same).heap_typed, metadata.trans (preserved value same).heap_extends⟩)
          (frame.trans tailFrame)
  · subst outcome
    have rawLess : rawSize < size := by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    have rawWithin : rawSize ≤ budget := Nat.le_trans (Nat.le_of_lt rawLess) within
    obtain ⟨native, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, rawPost⟩ :=
      rawMeaning rawSize rawWithin typed environments heaps locals agrees actualTyped initial admitted rawTrace
    cases represented with
    | @fault _ token matched =>
      have runs := CallableCoercionSpine.Runs.failure actual compilation.internalReason finalStore
        receipt.operand.type (.word token) (calls.map (CallableCoercionSpine.Call.rename ξ))
      rw [chain.final_type ξ] at runs
      exact ⟨_, finalStore, finalMap, finalWorld,
        (chain.spine.renamed_completed_iff ξ).mpr ⟨_, _, evaluated, runs⟩, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        by cases failure with
           | semantic => exact ⟨rawPost.rows, by intro _ impossible; cases impossible⟩
           | stage => exact rawPost⟩

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

include physical slots ownerFrame chain nonempty runtime typed environments heaps locals agrees actualTyped admitted in
theorem reflects (budget : Nat)
    (rawMeaning : ∀ size, size ≤ budget → RawReflectsAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : SelectedCompilationCoercionPathBounds.NativeBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (output.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission callerBridge.forgetSlots context node.type outcome reached := by
  obtain ⟨rawSize, native, middleStore, rawBound, _rawStrict, rawEvaluation, runs⟩ :=
    chain.spine.renamed_completed_sized ξ completed
  obtain ⟨sourceRawSize, rawOutcome, middle, middleMap, middleWorld, rawTrace, represented, middleHeaps,
      maps, worlds, frame, metadata, middleState, related, rawPost⟩ :=
    rawMeaning rawSize (Nat.le_trans rawBound within) typed environments heaps locals agrees actualTyped initial admitted rawEvaluation
  cases represented with
  | value valueRep =>
      have valueTyped := rawPost.at_value.1
      have middleTyped := rawPost.at_value.2.heap
      obtain ⟨pathSize, outcome, after, finalMap, finalWorld, pathTrace, result, finalHeaps,
          tailMaps, tailWorlds, tailFrame, tailMetadata, ⟨finalPool, tailRelated⟩, preserved⟩ :=
        SelectedCompilationCoercionPathBounds.reflects owner functions faults chain ownerFrame
          runtime (callerBridge.pool middleState) (physical middleState) (slots middleState)
          agrees middleHeaps valueRep middleTyped valueTyped
          (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
            (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
          budget bodyMeaning (runs.mono within)
      obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore middleState finalPool
        tailMaps tailWorlds tailFrame tailMetadata tailRelated
      have trace := Staging.Recursive.Size.Expression.coercedValue (lookupExpression?_sound receipt.found)
        nonempty rawTrace pathTrace
      exact ⟨_, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
        maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame, metadata.trans tailMetadata,
        returned, callerProtocol.trans related returnedRelated,
        after_expression_sized_of_preserved initial returned admitted trace (fun value same => ⟨(preserved value same).value_typed, (preserved value same).heap_typed, metadata.trans (preserved value same).heap_extends⟩) (frame.trans tailFrame)⟩
  | @fault failure token matched =>
      obtain ⟨sameValue, rfl⟩ := failed_runs runs
      rw [chain.final_type ξ] at sameValue
      subst value
      have trace := Staging.Recursive.Size.Expression.coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace
      exact ⟨_, _, middle, middleMap, middleWorld, trace, .fault matched, middleHeaps,
        maps, worlds, frame, metadata, middleState, related,
        by cases failure with
           | semantic => exact ⟨rawPost.rows, by intro _ impossible; cases impossible⟩
           | stage => exact rawPost⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedDirectExpressionBounds
