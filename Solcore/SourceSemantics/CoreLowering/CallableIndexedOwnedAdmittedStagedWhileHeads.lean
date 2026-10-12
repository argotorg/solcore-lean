import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileIterations
import Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileReadiness

/-! The authentic loop prelude installs a self cell without changing the Source
heap. Finite staged iterations retain its exact reached caller and state; a
fallthrough result returns to the original lexical context and environment. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CompatibleExpressionPrimitives (bool_fields)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchReflects BranchPreserves)
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr} {selfReason : Word}

include bridge functions condition transport in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → ReflectsAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (correct : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope statements expected type loopCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store ((LocalLoop.whileLoop type testCode loopCode selfReason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.While program stages sourceSize invocation context environment before test statements outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    ProtectedWhile.Body.Stateful.initial_state (protocol := callerProtocol)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions transport environments heaps locals agrees
      actualTyped read unmapped nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedWhileReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.2.2.2.1 installedRelated installedRecords admitted
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  rw [LoopRenaming.whileLoop] at completed
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := completed.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedWhileIterations.reflects bridge functions condition
      children found nodeType typed generated correct agrees reference entrySize
      (Nat.le_trans (Nat.le_of_lt entrySmaller) within) protectedState installedRead conditioned activated nativeEntry
  have total := installedProgress.trans progress
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    total.1, total.2.1, total.2.2.1, total.2.2.2.1, total.2.2.2.2,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

include bridge functions condition transport in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → PreservesAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (correct : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope statements expected type loopCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.While program stages size invocation context environment before test statements outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.whileLoop type testCode loopCode selfReason).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    ProtectedWhile.Body.Stateful.initial_state (protocol := callerProtocol)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions transport environments heaps locals agrees
      actualTyped read unmapped nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedWhileReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.2.2.2.1 installedRelated installedRecords admitted
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedWhileIterations.preserves bridge functions condition
      children found nodeType typed generated correct agrees reference size within protectedState
      installedRead conditioned activated trace
  have total := installedProgress.trans progress
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
    represented, total.1, total.2.1, total.2.2.1, total.2.2.2.1, total.2.2.2.2,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileHeads
