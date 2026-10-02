import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConstructors

/-! Registered constructor headers and the existing ordered packing tree close
native typing for recursive constructors with scalar children. The exact raw
metadata word is retained; no child-code typing callback is required. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping
open Core Frontend SourceInference
open CompatibleExpressionScalarNativeTyping

theorem packed_type (codes : List SourceCoreBasic.LoweredExpr) :
    (SourceCoreCalls.packArguments codes).type = SourceCoreCompatibleCatalog.packTypes (codes.map (·.type)) := by
  induction codes with
  | nil => rfl
  | cons head rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simp only [SourceCoreCalls.packArguments, SourceCoreCompatibleCatalog.packTypes, List.map_cons]
      exact congrArg (Ty.product head.type) ih

/-- The same ordered static sequence types zero, one and many arguments. Its
packing shape and inserted payload slots are the production helper's shape. -/
theorem packed_native {definitions : DataEnvironment} {nativeContext : Core.Context}
    {source : TypedSource} {certificates : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificates scope ids types codes)
    (children : ∀ id lowered, certificates scope id lowered → NativeTyping definitions nativeContext lowered) :
    NativeTyping definitions nativeContext (SourceCoreCalls.packArguments codes) := by
  induction tree with
  | nil => exact ⟨.unit, LanguageResult.success_hasType .unit⟩
  | single _ receipt => exact children _ _ receipt
  | cons _ receipt _ rest =>
    have first := children _ _ receipt
    exact ⟨.product first.1 rest.1, LocalSequence.pair_hasType first.1 rest.1 first.2 rest.2⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)

include visibleTypes in
theorem constructors_native
    (tree : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact conditionals_native visibleTypes administrative child
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children ih =>
    have sequence := CompatibleExpressionConstructors.sequence_of_nodes
      (scope := scope)
      (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) count nodes ih
    obtain ⟨packedWF, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
    have registered := receipt.registered
    rw [← packed_type codes] at registered
    obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
    exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

include visibleTypes in
theorem constructors_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := constructors_native visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include visibleTypes in
/-- The real contextual constructor traversal determines the tree and every
ordered child receipt. Source typing and visible scope annotations stay static
inputs, independently of native layout and metadata erasure. -/
theorem contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (syntaxTree : CompatibleExpressionConstructors.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  exact constructors_native_at visibleTypes administrative extension
    (CompatibleExpressionConstructors.tree_of_contextual ordinary unique closed residual declarations syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping
