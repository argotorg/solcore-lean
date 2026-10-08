import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport

/-! This same-Code receipt keeps only the static fields used by typed finish.
Its producer projects the genuine retained body and independent Syntax; no
body tree or Syntax is recovered from Code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues

structure Body {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) (program : Program)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    extends CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  flow : Expr
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
    compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
    (.initial compiled.compatible.checked) function.source
    (expressionSyntax function.source) (certificates readFuel function.source)
    compiled.indexed.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source
  syntaxTree : GenericImperativeMatch.Syntax function.source (expressionSyntax function.source)
    context (.statements true function.body) function.resultType

/-- This projection preserves the original Context, flow, tree and Code. -/
def Body.of_body_with {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative} {program : Program}
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates code program registry faults)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (expressionSyntax function.source)
      body.context (.statements true function.body) function.resultType) :
    Body code program expressionSyntax certificates where
  toContext := body.toContext
  frame := body.frame
  readFuel := body.readFuel
  flow := body.flow
  projection := body.projection
  emitted := body.emitted
  tree := body.tree
  valid := body.valid
  unique := body.unique
  syntaxTree := syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody
