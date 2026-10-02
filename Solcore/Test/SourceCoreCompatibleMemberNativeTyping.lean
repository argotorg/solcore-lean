import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping

/-! Heterogeneous packed fields retain complete callable carriers. The public
contextual consumer requires actual catalog/compiler acceptance and independent
source typing, without native child or branch typing callbacks. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMemberNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CompatibleExpressionMemberNativeTyping CompatibleExpressionScalarNativeTyping

theorem callable_field_stays_one_packed_field (definitions : DataEnvironment) :
    HasType [SourceCoreCompatibleCatalog.packTypes [.word,
        CallableContract.functionType .bool .bool, .namedData ⟨27⟩]]
      (SourceCoreDataExpressions.projectPacked 1 [.word, CallableContract.functionType .bool .bool, .namedData ⟨27⟩] (.var 0))
      (CallableContract.functionType .bool .bool) definitions :=
  projectPacked_native (by rfl) (.var rfl)

theorem tagged_callable_field_stays_one_packed_field (definitions : DataEnvironment) :
    HasType [SourceCoreCompatibleCatalog.packTypes [.unit,
        TaggedFunction.functionType .word .integer, .cell .bool]]
      (SourceCoreDataExpressions.projectPacked 1 [.unit, TaggedFunction.functionType .word .integer, .cell .bool] (.var 0))
      (TaggedFunction.functionType .word .integer) definitions :=
  projectPacked_native (by rfl) (.var rfl)

theorem actual_contextual_members_native
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment} (administrative : Core.Context)
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (ordinary : CompatibleExpressionMembers.Ordinary source locals compilation.owner)
    (unique : SourceSemantics.NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionMembers.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : SourceSemantics.ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  contextual_native visibleTypes administrative registered ordinary unique closed residual declarations sourceSignatures
    syntaxTree found sourceTyped readPolicy lowerPolicy leafPolicy accepted extension

end Tests.SourceCoreCompatibleMemberNativeTyping
