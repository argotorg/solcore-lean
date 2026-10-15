import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsProjectedAssignmentLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsLexicalLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsDiscardLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForHeaderLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageForLiftBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (ItemShape)
open GenericForHeader (Tree)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)

include bridge functions faithful observations definitions registered producer acquire transport extension in
/-- Every actual post-header item preserves its ordered allocation, evaluation
and write. The loop caller restores its bindings only after this vector ends. -/
theorem lifts {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context childSize,
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
        bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {administrative : Core.Context} {control : ControlContext}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    (shape : ItemShape items)
    (sourceTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context items) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition items budget := by
  revert shape sourceTyped
  induction tree with
  | nil next =>
    intro _ _
    exact SelectedCompilationStageForItemsDiscardLifting.nil bridge functions condition
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same tail ih =>
    intro shape sourceTyped
    exact SelectedCompilationStageForItemsLexicalLifting.absent bridge functions definitions registered producer condition acquire
      mono extended ordinary projected allocation annotation same
      (ih shape.let_tail (CallableIndexedOwnedPreparedStagedForItemsTyping.absent sourceTyped extended))
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same tail ih =>
    intro shape sourceTyped
    obtain ⟨node, nodeFound, typed, generated⟩ := child
    cases Option.some.inj (found.symm.trans nodeFound)
    exact SelectedCompilationStageForItemsLexicalLifting.initialized bridge functions definitions registered producer condition acquire
      mono extended ordinary found sourceType typed generated allocation annotation same (children context) (preservation context)
      (ih shape.let_tail (CallableIndexedOwnedPreparedStagedForItemsTyping.initialized sourceTyped mono extended))
  | @discard context scope expression expressionNode rest lowered body found child tail ih =>
    intro shape sourceTyped
    obtain ⟨node, nodeFound, typed, generated⟩ := child
    cases Option.some.inj (found.symm.trans nodeFound)
    exact SelectedCompilationStageForItemsDiscardLifting.lifts bridge functions condition found typed generated
      (children context) (preservation context)
      (ih shape.discard_tail (CallableIndexedOwnedPreparedStagedForItemsTyping.expression sourceTyped))
  | @assign context scope assignment operator rhs rest body head tail ih =>
    intro shape sourceTyped
    obtain ⟨_profile, tailShape⟩ := shape.assignment_tail
    have typedChildren (size : Nat) (smaller : size < budget) :
        LiftsAt bridge context model stages invocation (TypedCertificate invocation.source certificates context) size := by
      intro scope id lowered generated node found typed
      obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
      exact children context size smaller certified found typed
    have typedPreservation (size : Nat) :
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
      intro scope id lowered generated node found typed
      obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
      exact preservation context size certified found typed
    intro size within
    by_cases bare : assignment.target.projections = []
    · exact SelectedCompilationStageForItemsAssignmentLifting.lifts bridge functions transport extension condition
        unique head bare (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
        typedChildren typedPreservation
        (ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2) within
    · exact SelectedCompilationStageForItemsProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension condition
        unique head bare (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
        typedChildren typedPreservation
        (ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2) within
  | @bitNot context scope assignment rest body head tail ih =>
    intro shape sourceTyped
    obtain ⟨_rawWord, _bare, tailShape⟩ := shape.bitNot_tail
    exact SelectedCompilationStageForItemsBitNotLifting.lifts bridge functions transport condition
      head (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      (ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForHeaderLifting
