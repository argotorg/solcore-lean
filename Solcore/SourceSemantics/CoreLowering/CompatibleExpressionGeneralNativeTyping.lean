import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionDataLeafNativeTyping
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualGeneral

/-! The existing recursive grammars type their own child code at every position.
Constructor packing, member rows and general mapping comparators retain the
actual factory receipts. Source-static trees contain no native typing callbacks. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionScalarNativeTyping CompatibleExpressionMemberNativeTyping
open CompatibleExpressionConstructorNativeTyping CompatibleExpressionDataLeafNativeTyping
open CompatibleCatalogNominalCoverage

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

private theorem constructor_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {context : Core.Context}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
    (children : ∀ child code, (child, code) ∈ ids.zip codes →
      NativeTyping values.checked.catalog.definitions context code) :
    NativeTyping values.checked.catalog.definitions context
      ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ := by
  have sequence := CompatibleExpressionConstructors.sequence_of_nodes
    (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions context code)
    count nodes children
  obtain ⟨_, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
  have registered := receipt.registered
  rw [← packed_type codes] at registered
  obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
  (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)

include shaped complete visibleTypes in
theorem recursive_native
    (tree : CompatibleExpressionRecursive.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact members_native shaped complete visibleTypes administrative child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩

include shaped complete visibleTypes in
theorem general_native
    (tree : CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | proxy receipt => exact proxy_native receipt _
  | fragment child => exact recursive_native shaped complete visibleTypes administrative child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩
  | index header _ _ _ _ _ first second => exact index_native header first second (reasonAt _)

include shaped complete visibleTypes in
theorem recursive_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionRecursive.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := recursive_native shaped complete visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include shaped complete visibleTypes in
theorem general_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := general_native shaped complete visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include visibleTypes in
theorem contextual_native
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionGeneral.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionGeneral.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  have shaped := prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  exact general_native_at shaped (prepare_complete registered) visibleTypes administrative extension
    (CompatibleExpressionGeneral.tree_of_contextual ordinary unique closed residual declarations sourceSignatures syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralNativeTyping
