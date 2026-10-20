import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyInitialized
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyConditional
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDiscard
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation

/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include definitions registered extension uninitialized semantic selectedBodies in
theorem completes {context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError (.initial checked) invocation.source
      (CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt))
      context scope mode statements expected type code) :
    ∀ entry : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result entry registry faults mode statements expected type code) := by
  induction tree with
  | nil allowed =>
    intro entry
    exact CellAwareLexicalBodyLeaves.nil entry allowed
  | returnUnit rest found form =>
    intro entry
    exact CellAwareLexicalBodyLeaves.returnUnit entry rest found form
  | returnValue rest found form expressionFound valueType value =>
    intro entry
    exact CellAwareLexicalBodyLeaves.terminal extension uninitialized semantic selectedBodies entry
      (.returning rest found form) expressionFound valueType value
  | tail found form expressionFound valueType value =>
    intro entry
    exact CellAwareLexicalBodyLeaves.terminal extension uninitialized semantic selectedBodies entry
      (.tail found form) expressionFound valueType value
  | uninitialized found form mono extended ordinary projected allocation annotation same remaining ih =>
    intro entry
    exact CellAwareLexicalBodyDeclarations.absent definitions registered entry found form mono extended ordinary
      projected allocation annotation same ih
  | initialized found form mono extended ordinary initializerFound sourceType initial allocation annotation same remaining ih =>
    intro entry
    exact CellAwareLexicalBodyInitialized.completes definitions registered extension uninitialized semantic selectedBodies
      entry found form mono extended ordinary initializerFound sourceType initial allocation annotation same ih
  | discard found form notTail continuing expressionFound value remaining ih =>
    intro entry
    exact CellAwareLexicalBodyDiscard.completes extension uninitialized semantic selectedBodies
      entry found form continuing expressionFound value ih
  | block found form inner remaining innerIH restIH =>
    intro entry
    exact CellAwareLexicalBodyBlock.completes entry found form innerIH restIH
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH restIH =>
    intro entry
    exact CellAwareLexicalBodyConditional.completes extension uninitialized semantic selectedBodies
      entry found form conditionFound conditionType conditionTree thenIH elseIH (.inl restIH)
  | terminalBlock unique found form inner stops issued innerIH =>
    intro entry
    exact CellAwareLexicalBodyBlock.stopped entry found form stops innerIH
  | terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    intro entry
    exact CellAwareLexicalBodyConditional.completes extension uninitialized semantic selectedBodies
      entry found form conditionFound conditionType conditionTree thenIH elseIH (.inr ⟨thenStops,elseStops⟩)

include definitions registered extension uninitialized semantic selectedBodies in
theorem reflects {context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError (.initial checked) invocation.source
      (CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt))
      context scope mode statements expected type code)
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    {value : Value} {finalStore : Store}
    (completed : Evaluates entry.actual entry.store (code.rename entry.embedding) value finalStore) :
    ∃ result : Result entry registry faults mode statements expected type code,
      result.value = value ∧ result.store = finalStore := by
  obtain ⟨result⟩  := completes (registry := registry) definitions registered extension uninitialized semantic selectedBodies tree entry
  have same := evaluation_deterministic result.evaluated completed
  exact ⟨result,same⟩

include definitions registered extension uninitialized semantic selectedBodies in
theorem preserves {context scope mode statements expected type code}
    (tree : CellAwareOrdinaryBodyTree.Tree layouts owner active frame globals onError (.initial checked) invocation.source
      (CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation) (reasonAt := reasonAt))
      context scope mode statements expected type code)
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    {size finalContext outcome after}
    (trace : Staging.Recursive.Size.StatementsIn program registry mode size invocation context entry.environment entry.heap
      statements finalContext outcome after) :
    ∃ result : Result entry registry faults mode statements expected type code,
      finalContext = result.finalContext ∧ outcome = result.outcome.embed ∧ after = result.after := by
  obtain ⟨result⟩ := completes (registry := registry) definitions registered extension uninitialized semantic selectedBodies tree entry
  exact ⟨result,result.determines trace⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyCompletion
