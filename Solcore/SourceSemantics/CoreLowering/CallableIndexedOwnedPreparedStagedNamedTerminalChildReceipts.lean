import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedContextualProductReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds

/-! The actual accepted named body retains the same compiled terminal child.
Independent Source program typing authenticates that child's original raw
result type. The genuine parameter scope and production contextual compiler
construct its finite read/literal/group/pair receipt with literal sites. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include terminal selected wellFormed in
/-- Complete original Source typing selects the same used terminal occurrence
and its raw result type at the actual parameter context. -/
theorem source_child :
    ∃ node, header.function.source.lookupExpression? expression = some node ∧
      node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context expression node.type := by
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨final, facts, typed, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [← stages.source selected] at typed
  obtain ⟨node, found, rawType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique
      (terminal.head child (stages.source selected)) typed complete
  rw [stages.source selected] at found childTyped
  exact ⟨node, found, rawType, childTyped⟩

include aligned terminal selected wellFormed in
/-- Accepted Header lowering constructs the actual finite child tree.
Ordinary catalog exclusions remain static Source metadata conditions. The
used code, result type and each literal site belong to the original callback. -/
theorem finite_child
    (ordinary : CompatibleExpressionProducts.Ordinary header.function.source
      compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner)
    (syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression) :
    CompatibleExpressionProducts.Tree.WithLiterals
      (fuel := compiled.indexed.fuel)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (source := header.function.source) (context := header.context)
      (solved := header.solved) (reasonAt := header.reasonAt)
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate header.solved header.function.source id lowered)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression terminal.child := by
  obtain ⟨node, found, _rawType, typed⟩ := source_child terminal selected wellFormed
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry)
    (program := Program.ofChecked compiled.sourceProgram) header
  have accepted := terminal.generated
  have expressionPolicy : header.policy.lowerExpression =
      (RecursiveNamedPreparedHeaders.Prepared.policy prepared).lowerExpression :=
    congrArg SourceCoreLoops.Policy.lowerExpression aligned.policy
  rw [expressionPolicy] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    prepared.compilation.parents prepared.compilation.own.assignments prepared.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
    compiled.indexed.base.callableContext none none terminal.childFuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok terminal.child at accepted
  have tree := CallableIndexedOwnedPreparedStagedContextualProductReceipts.of_contextual
    (readFuel := compiled.indexed.fuel)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    ordinary header.unique declarations syntaxTree found typed rfl rfl rfl accepted
  simpa only [aligned.solved, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext, RecursiveNamedCatalogNativeContexts.bodyScope] using tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
