import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionPathLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalRawDirectBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedExpressionLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open SelectedCompilationPhysicalRawDirectBounds (RawPreservesAt)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)
open SelectedCompilationStageCoercionLiftBounds
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
theorem lifts (budget : Nat)
    (rawLift : ∀ {size plain after}, RawOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      invocation.source environment before node.form node.requirements node.coercions plain after → size ≤ budget →
      RawLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before
        node.form node.requirements node.coercions plain after)
    (rawPreservation : ∀ size, RawPreservesAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size)
    (bodyMeaning : SelectedCompilationStageCoercionPathLifting.LiftBodies
      (headers := headers) (receiving := receiving) owner functions chain budget)
    (bodyPreservation : ∀ grade, SelectedCompilationCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain grade)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      invocation.source environment before id outcome after) (within : size ≤ budget) :
    Staging.Recursive.Lifting.ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context
      environment before id outcome after := by
  cases SelectedCompilationStageCoercedSource.branches unique receipt.found receipt.form trace with
  | fault raw smaller =>
    obtain ⟨staged, reached, rawTrace, adapted⟩ := rawLift raw (Nat.le_trans (Nat.le_of_lt smaller) within)
    cases adapted with
    | completed => exact ⟨_, _, .coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace, .rejected origin call reason _⟩
  | value raw path rawLess pathLess =>
    obtain ⟨staged, reachedHeap, rawTrace, adapted⟩ := rawLift raw (Nat.le_trans (Nat.le_of_lt rawLess) within)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .coercedFault (lookupExpression?_sound receipt.found) nonempty rawTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨grade, sized⟩ := Staging.Recursive.Size.RawForm.of_trace rawTrace
      obtain ⟨native, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          _maps, _worlds, frame, _metadata, middleState, _related, rawPost⟩ :=
        rawPreservation grade typed environments heaps locals agrees actualTyped initial admitted sized
      cases represented with
      | value valueRep =>
        obtain ⟨staged, reachedHeap, pathTrace, adapted⟩ :=
          SelectedCompilationStageCoercionPathLifting.lifts owner functions faults chain ownerFrame runtime ledger
            (callerBridge.pool middleState) (physical middleState) (slots middleState) agrees middleHeaps valueRep
            rawPost.at_value.2.heap rawPost.at_value.1
            (CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
              (callerBridge.pool initial) (callerBridge.pool middleState) admitted.rows frame)
            budget bodyMeaning bodyPreservation path (Nat.le_trans (Nat.le_of_lt pathLess) within)
        exact ⟨staged, reachedHeap,
          .coercedValue (lookupExpression?_sound receipt.found) nonempty rawTrace pathTrace, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedExpressionLifting
