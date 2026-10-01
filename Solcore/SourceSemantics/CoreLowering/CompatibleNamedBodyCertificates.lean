import Solcore.SourceSemantics.CoreLowering.CompatibleStatementCertificates

/-! Static receipts for the ordinary fixed-scope named-body fragment. A receipt
retains the actual production traversal equation and its extracted statement
tree at one source context. It contains no body execution or semantic induction
hypothesis. Context/evidence validity remains a separate static obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
open Core Frontend SourceInference

structure Certificate (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (policy : SourceCoreLoops.Policy) (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    type reasonAt fellThrough escaped = .ok code
  flow : Expr
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : CompatibleStatements.Tree readFuel values source context solved reasonAt scope
    statements expected type flow

/-- Extract the body tree from the actual contextual compiler. Every remaining
premise concerns source syntax, typing, context, or a production policy field. -/
theorem of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : CompatibleStatements.Syntax source context statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    Nonempty (Certificate readFuel values source context compilation.solvedRequirements reasonAt scope
      statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, emitted, tree⟩ := CompatibleStatements.tree_of_contextual_body ordinary unique closed residual
    declarations readExpression lowerRead leafLowerer readStatement lowerExpression syntaxTree projection accepted
  exact ⟨⟨accepted, flow, emitted, tree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
