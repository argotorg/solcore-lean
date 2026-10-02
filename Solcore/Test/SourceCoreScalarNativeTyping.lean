import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping

/-! External consumers derive complete native annotations from the production
contextual traversal. The negative fixture distinguishes visible cell types
from runtime typing; shadowed and administrative annotations are unconstrained.
The existing conditional and compatible-read IO suites exercise this same code. -/
set_option autoImplicit false
namespace Tests.SourceCoreScalarNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionScalarNativeTyping

/-- No static lowering tree or per-child native typing premise is supplied by
the consumer. Root and specialized parent callbacks use the same entry point. -/
theorem actual_contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (ordinary : CompatibleExpressionConditionals.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : CompatibleExpressionConditionals.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    lowered.type.WellFormed definitions ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions :=
  contextual_native visibleTypes administrative ordinary unique declarations syntaxTree found typed
    readPolicy lowerPolicy leafPolicy accepted extension

/-- The same induction closes all scalar children inside another static
consumer, under arbitrary hidden slots and an ambient data extension. -/
theorem all_children_native
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  conditionals_native_at visibleTypes administrative extension tree

private def missing : Ty := .namedData ⟨0⟩

/-- Runtime typing of an inhabited sum leaves its unused annotation unchecked.
It cannot supply the visible annotation needed by a lazy default/read. -/
theorem runtime_typing_does_not_authenticate_scope (binder : Resolved.LocalId) :
    RuntimeValueHasType [] (.inLeft missing .unit) (.sum .unit missing) [] ∧
      ¬ ScopeWellFormed [] [(binder, .sum .unit missing)] := by
  refine ⟨.inLeft .unit, ?_⟩
  intro typed
  have found : SourceCoreLocalCell.lookup? [(binder, .sum .unit missing)] binder =
      some (0, .sum .unit missing) := by simp [SourceCoreLocalCell.lookup?]
  have wellFormed := typed binder 0 (.sum .unit missing) found
  cases wellFormed with
  | sum _ invalid => cases invalid with | namedData found => cases found

/-- An invalid annotation hidden by the actual first-match scope lookup is
irrelevant. No requirement is imposed on the complete native context. -/
theorem shadowed_annotation_allowed (binder : Resolved.LocalId) :
    ScopeWellFormed [] [(binder, .bool), (binder, missing)] := by
  intro selected index type found
  by_cases same : binder = selected
  · simp [SourceCoreLocalCell.lookup?, same] at found
    obtain ⟨rfl, rfl⟩ := found
    constructor
  · simp [SourceCoreLocalCell.lookup?, same] at found

end Tests.SourceCoreScalarNativeTyping
