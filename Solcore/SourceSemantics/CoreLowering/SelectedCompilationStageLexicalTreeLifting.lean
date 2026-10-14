import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBlockLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalTreeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape)
open GenericLexicalStatements (Tree)
open TypedLexicalControl (sequence_rename)
universe u

open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
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

open SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves)

include bridge bindings definitions registered producer acquire in
theorem branch_preservation
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
    (unique : NodeOccurrencesUnique invocation.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates) context scope false statements expected type code)
    (shape : Shape invocation.source false statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {administrative : Core.Context} :
    ∀ size, BranchPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope statements expected type code size := by
  intro size childSize within
  exact CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation.preserves bridge bindings functions definitions
    registered producer condition acquire (fun context n _ => preservation context n) unique tree shape projection within

include bridge bindings definitions registered producer acquire in
theorem lifts {budget : Nat}
    (children : ∀ context childSize, childSize < budget → LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
    (unique : NodeOccurrencesUnique invocation.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates) context scope mode statements expected type code)
    (shape : Shape invocation.source mode statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {administrative : Core.Context} :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode statements budget := by
  induction tree generalizing administrative with
  | nil allowed => exact SelectedCompilationStageScopedTerminalLifting.nil bridge functions condition
  | returnUnit rest found form => exact SelectedCompilationStageScopedTerminalLifting.return_unit bridge functions condition unique found form
  | returnValue rest found form expressionFound valueType child =>
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have same := Option.some.inj (expressionFound.symm.trans typedFound)
    cases same
    intro size within
    exact SelectedCompilationStageScopedTerminalLifting.terminal bridge functions condition unique
      (.returning rest (lookupStatement?_sound found) form) expressionFound typed certified (children _) within
  | tail found form expressionFound valueType child =>
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have same := Option.some.inj (expressionFound.symm.trans typedFound)
    cases same
    intro size within
    exact SelectedCompilationStageScopedTerminalLifting.terminal bridge functions condition unique
      (.tail (lookupStatement?_sound found) form) expressionFound typed certified (children _) within
  | uninitialized found form mono extended ordinary projected allocation annotation same tail ih =>
    exact SelectedCompilationStageLexicalLifting.absent bridge functions definitions registered producer condition acquire
      unique found form mono extended ordinary projected allocation annotation same (ih (shape.tail_of_let found form) projection)
  | initialized found form mono extended ordinary initialFound sourceType child allocation annotation same remaining ih =>
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
    cases nodeEq
    intro size within
    exact SelectedCompilationStageLexicalLifting.initialized bridge functions definitions registered producer condition acquire
      unique found form mono extended ordinary initialFound sourceType typed certified allocation annotation same
      (children _) (preservation _) (ih (shape.tail_of_let found form) projection) within
  | discard found form guard expressionFound child remaining ih =>
    obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have same := Option.some.inj (expressionFound.symm.trans typedFound)
    cases same
    intro size within
    exact SelectedCompilationStageDiscardLifting.lifts bridge functions condition unique found form continuing
      expressionFound typed certified (children _) (preservation _) (ih tailShape projection) within
  | block found form inner remaining innerIH remainingIH =>
    obtain ⟨innerShape, restShape⟩ := shape.block_children found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (innerIH innerShape projection)
      (branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique inner innerShape projection)
      (.inl (remainingIH restShape projection))
  | @ifThen context scope mode id node test testNode left right rest expected type testCode leftCode rightCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    have same := Option.some.inj (conditionFound.symm.trans typedFound)
    cases same
    apply SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then leftCode else rightCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _)
    · intro truth; cases truth
      · exact elseIH rightShape projection
      · exact thenIH leftShape projection
    · intro truth; cases truth
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique elseTree rightShape projection
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique thenTree leftShape projection
    · exact .inl (remainingIH restShape projection)
  | terminalBlock exactUnique found form inner stops issued ih =>
    obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (ih innerShape projection)
      (branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique inner innerShape projection)
      (.inr stops)
  | @terminalIf context scope mode id node test testNode left right rest expected type testCode leftCode rightCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    have same := Option.some.inj (conditionFound.symm.trans typedFound)
    cases same
    apply SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then leftCode else rightCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _)
    · intro truth; cases truth
      · exact elseIH rightShape projection
      · exact thenIH leftShape projection
    · intro truth; cases truth
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique elseTree rightShape projection
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique thenTree leftShape projection
    · exact .inr ⟨thenStops, elseStops⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalTreeLifting
