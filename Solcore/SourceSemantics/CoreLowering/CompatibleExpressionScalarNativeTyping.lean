import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConditionals
import Solcore.Core.DefinitionExtension

/-! Native typing for the existing literal/read/product/primitive/conditional
families. Visible native scope types supply the complete annotations needed by
lazy mapping defaults. Every child code is typed by the same static tree's
induction, under arbitrary administrative contexts and ambient extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev Scope := SourceCoreLocalCell.Scope

/-- Only actually visible source-cell payload types are constrained. Native
administrative types and runtime value typing do not authenticate these types. -/
def ScopeWellFormed (definitions : DataEnvironment) (scope : Scope) : Prop :=
  ∀ binder index type, SourceCoreLocalCell.lookup? scope binder = some (index, type) →
    type.WellFormed definitions

theorem ScopeWellFormed.empty (definitions : DataEnvironment) : ScopeWellFormed definitions [] := by
  intro binder index type found
  cases found

theorem ScopeWellFormed.prepend {definitions : DataEnvironment} {scope : Scope}
    (typed : ScopeWellFormed definitions scope) (binder : Resolved.LocalId) {type : Ty}
    (wellFormed : type.WellFormed definitions) : ScopeWellFormed definitions ((binder, type) :: scope) := by
  intro selected index payload found
  by_cases same : binder = selected
  · simp [SourceCoreLocalCell.lookup?, same] at found
    obtain ⟨rfl, rfl⟩ := found
    exact wellFormed
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at found
    cases tail : SourceCoreLocalCell.lookup? scope selected with
    | none => simp [tail] at found
    | some pair =>
      obtain ⟨previous, payloadType⟩ := pair
      simp only [tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact typed _ _ _ tail

def NativeTyping (definitions : DataEnvironment) (context : Core.Context)
    (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  lowered.type.WellFormed definitions ∧
    HasType context lowered.expression (LanguageResult.resultType lowered.type) definitions

theorem literal_native {solved : List SolvedRequirement} {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code)
    (definitions : DataEnvironment) (context : Core.Context) :
    NativeTyping definitions context ⟨type, code⟩ := by
  cases literal <;> exact ⟨by constructor, LanguageResult.success_hasType (by constructor)⟩

theorem read_native {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word} {scope : Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (read : CompatibleExpressionReads.LoweredRead fuel values source sourceContext reasonAt scope id lowered)
    (typed : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨certificate, same, binding⟩ := read
  have wellFormed := typed _ _ _ certificate.slot
  refine ⟨same ▸ wellFormed, ?_⟩
  rw [← same]
  exact certificate.native_hasType binding wellFormed administrative

private theorem binary_native {definitions : DataEnvironment} {context : Core.Context}
    {mode : Mode} {operator : Syntax.BinaryOp} {left right : Expr}
    (first : HasType context left (LanguageResult.resultType (mode.operandType operator)) definitions)
    (second : HasType context right (LanguageResult.resultType (mode.operandType operator)) definitions) :
    NativeTyping definitions context ⟨mode.resultType operator, mode.binary operator left right⟩ := by
  constructor
  · cases mode <;> cases operator <;> constructor
  · cases mode with
    | word => exact SourceCorePrimitive.binary_hasType first second
    | integer => exact SourceCoreInteger.binary_hasType first second

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (typed : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)
include typed in
theorem products_native
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | literal receipt =>
    obtain ⟨_, _, literal⟩ := receipt
    exact literal_native literal _ _
  | read receipt => exact read_native receipt typed administrative
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩

include typed in
theorem primitives_native
    (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | product child => exact products_native typed administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2

include typed in
theorem conditionals_native
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | primitive child => exact primitives_native typed administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩

include typed in
theorem conditionals_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := conditionals_native typed administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include typed in
/-- The production contextual traversal supplies every child certificate.
Visible cell annotations are the only additional native typing input; neither
an independently supplied tree nor a child-code typing callback is needed. -/
theorem contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionConditionals.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (syntaxTree : CompatibleExpressionConditionals.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead fuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  exact conditionals_native_at typed administrative extension
    (CompatibleExpressionConditionals.tree_of_contextual ordinary unique declarations syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)
end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping
