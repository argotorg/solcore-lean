import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedContextualProductReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds

/-! The actual accepted named body retains the same compiled terminal child.
Independent Source program typing authenticates that child's original raw
result type. The genuine parameter scope and production contextual compiler
construct its finite read/literal/group/pair receipt with literal sites. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalChildReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)

include terminal selected certified in
/-- Complete original Source typing selects the same used terminal occurrence
and its raw result type at the actual parameter context. -/
theorem source_child :
    ∃ node, header.function.source.lookupExpression? expression = some node ∧
      node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context expression node.type := by
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨final, facts, typed, complete⟩ := certified.statements
  rw [← stages.source selected] at typed
  obtain ⟨node, found, rawType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique
      (terminal.head child (stages.source selected)) typed complete
  rw [stages.source selected] at found childTyped
  exact ⟨node, found, rawType, childTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalChildReceipts
