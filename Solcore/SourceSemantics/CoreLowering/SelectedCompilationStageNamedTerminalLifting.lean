import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalChildReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedTerminalSupport
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
open SelectedCompilationStageBodyLiftBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {terminal : Terminal header}
  (static : SelectedCompilationPhysicalMixedNamedTerminalSupport.Support
    (headers := headers) (stages := stages) (semanticFaults := semanticFaults) header terminal)
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)

local notation "physicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)

include static selected certified in
/-- The actual terminal statement selects one strictly smaller ordinary child.
The internal root induction lifts it before reconstructing the same return. -/
theorem lifts {budget : Nat}
    (children : ∀ size, size < budget →
      LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner _packet keyPhysical physical slots
    size finalContext outcome after trace within
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have originalTerminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      child.source terminal.expression header.function.body := by
    rw [stages.source selected]
    exact terminal.receipt.terminal
  obtain ⟨childSize, plain, strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique originalTerminal trace
  subst finalContext
  subst outcome
  let entered : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, before, store, canonical⟩ := ⟨⟨initial, slots⟩, physical⟩
  have enteredAdmission : Admission physicalBridge header.context entered := ⟨admitted.heap, admitted.rows⟩
  obtain ⟨node, found, _rawType, sourceTyped⟩ :=
    SelectedCompilationNamedTerminalChildReceipts.source_child terminal.receipt selected certified
  rw [← stages.source selected] at found sourceTyped
  let root := (static.roots child selected).val
  have meaning : LiftsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      header.context model stages child
      (Point (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        terminal.expression terminal.receipt.child) childSize :=
    children childSize (Nat.lt_of_lt_of_le strict within) root owner keyPhysical
  have prefixEq : root.compilation.administrativePrefix = 1 := (static.roots child selected).property.2.2
  rw [prefixEq] at meaning
  have lifted := meaning ⟨rfl, rfl, rfl⟩ found sourceTyped environments heaps locals agrees typed
    entered enteredAdmission evaluated
  exact terminal_expression (terminal.receipt.head child (stages.source selected)) lifted

include selected in
/-- A factory's actual terminal lambda has no callable-body execution at
formation time. The ordinary atomic trace lifts with the same captures. -/
theorem formation {bodyRegistry : SourceCoreRawMetadata.Registry}
    (formation : SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
      header terminal) {budget : Nat} :
    NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    _environments _heaps _locals _agrees _typed _initial _admitted _owner _packet _keyPhysical _physical _slots
    size finalContext outcome after trace _within
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have originalTerminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      child.source terminal.expression header.function.body := by
    rw [stages.source selected]
    exact terminal.receipt.terminal
  obtain ⟨_childSize, plain, _strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique originalTerminal trace
  subst finalContext
  subst outcome
  obtain ⟨receipt⟩ := formation.formations child selected
  cases receipt with
  | inl receipt =>
    have found : child.source.lookupExpression? terminal.expression = some receipt.site.code.sourceNode := by
      simpa only [stages.source selected, header.agreement.source, receipt.identifier,
        CallableIndexedLambdaGeneration.closure, CallableIndexedNamedGeneration.source] using receipt.site.code.sourceFound
    have lifted := Staging.Recursive.Lifting.atomic_nonlocal (registry := stages)
      unique (lookupExpression?_sound found)
      (receipt.site.code.sourceForm.symm ▸ Staging.Recursive.AtomicForm.lambda _ _ _)
      receipt.coercions
      (by intro name binder same; rw [receipt.site.code.sourceForm] at same; cases same)
      evaluated.sound
    exact terminal_expression (terminal.receipt.head child (stages.source selected))
      (Staging.Recursive.Lifting.ExpressionLift.completed lifted)
  | inr receipt =>
    have found : child.source.lookupExpression? terminal.expression = some receipt.produced.site.code.sourceNode := by
      simpa only [stages.source selected, header.agreement.source, receipt.produced.identifier,
        CallableIndexedLambdaGeneration.closure, CallableIndexedNamedGeneration.source] using receipt.produced.site.code.sourceFound
    have lifted := Staging.Recursive.Lifting.atomic_nonlocal (registry := stages)
      unique (lookupExpression?_sound found)
      (receipt.produced.site.code.sourceForm.symm ▸ Staging.Recursive.AtomicForm.lambda _ _ _)
      receipt.coercions
      (by intro name binder same; rw [receipt.produced.site.code.sourceForm] at same; cases same)
      evaluated.sound
    exact terminal_expression (terminal.receipt.head child (stages.source selected))
      (Staging.Recursive.Lifting.ExpressionLift.completed lifted)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedTerminalLifting
