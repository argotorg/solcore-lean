import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationStageBodyLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)

private theorem terminal_of_head {child : Staging.Recursive.Scope} {expression : ExpressionId}
    {statements : List StatementId} (unique : NodeOccurrencesUnique child.source)
    (head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression statements) :
    CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal child.source expression statements := by
  cases head with
  | returning rest contains form => exact .returning rest (lookupStatement?_complete unique contains) form
  | tail contains form => exact .tail (lookupStatement?_complete unique contains) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)

private abbrev parameterScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
local notation "physicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

/-- The actual closure parameter entry supplies this physical state. Its
complete capture environment and real frame stay in the original closure. -/
def ClosureLiftsBelow (budget : Nat) : Prop :=
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ contextLocation native},
    DataHeap.EnvRepresents catalog mapping world administrativeContext (parameterScope code) environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before inputs.context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
    canonical[(parameterScope code).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation) →
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) →
    contextLocation ∉ mapping →
    CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native →
  ∀ initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨(parameterScope code), mapping, world, before, store, canonical⟩,
    Admission physicalBridge inputs.context initial →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
  ∀ {size finalContext outcome after},
    RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked compiled.sourceProgram) size inputs.context
      child.evidence child.source environment before function.body finalContext outcome after →
    size ≤ budget →
    BodyLift (Program.ofChecked compiled.sourceProgram) stages true child inputs.context environment before
      function.body finalContext outcome after

variable {semanticFaults : FunctionCalls.FaultRep}
  {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
  (support : SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers) code inputs stages packet semanticFaults)
  (selected : stages.Closure function child) (owner : OwnedKey keys)
  (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)

include support selected ownerPhysical in
/-- The same closure packet exposes its original terminal statement and
strict expression child at the genuine allocated parameter state. -/
theorem terminal {budget : Nat}
    (children : ∀ size, size < budget →
      LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size) :
    ClosureLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget := by
  intro mapping world administrativeContext environment canonical actual actualContext before store ξ contextLocation native
    environments heaps locals agrees typed _reference _read _unmapped _conditioned initial admitted valid size finalContext outcome after trace within
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  have head := CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head packet.receipt view
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  obtain ⟨node, found, _sameType, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped completes
  have original := terminal_of_head unique head
  obtain ⟨childSize, plain, strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique original trace
  subst finalContext
  subst outcome
  have meaning : LiftsAt physicalBridge inputs.context model stages child
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point (parameterScope code)
        packet.expression packet.receipt.child) childSize :=
    children childSize (Nat.lt_of_lt_of_le strict within) (support.rootAt child selected) owner ownerPhysical
  have lifted := meaning ⟨rfl, rfl, rfl⟩ found sourceTyped environments heaps locals agrees typed
    initial admitted evaluated
  exact terminal_expression head lifted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureBodyLifting
