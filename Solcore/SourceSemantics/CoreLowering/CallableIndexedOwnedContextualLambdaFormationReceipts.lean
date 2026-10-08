import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProducerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeads

/-! Formation retains the actual chosen Site rather than a later code-shaped
replacement. Binder policy comes from the original contextual producer; full
Syntax is an independent static receipt at the same body context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The original ordinary formation plus the two static facets it omitted. -/
structure OrdinaryFormation
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.Formation
      (registry := registry) (faults := faults) caller context evidence scope id lowered where
  binderPolicy : BinderPolicy caller.named site.code
  syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source caller.named)
    (expressionSyntax (CallableIndexedNamedGeneration.source caller.named)) body.context
    (.statements true statements) result

/-- The principal formation already retained its full Syntax. -/
structure PrincipalFormation {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedMethodLambdaExpressionHeads.Formation
      (registry := registry) (faults := faults) principal context scope id lowered where
  binderPolicy : BinderPolicy principal.named site.code

theorem OrdinaryFormation.at
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryFormation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) :
    OrdinaryAt (receipt.toFormation.code environment) (receipt.toFormation.support environment) :=
  .recaptured caller receipt.site receipt.expressionSyntax receipt.certificates receipt.body
    receipt.binderPolicy receipt.syntaxTree environment

theorem PrincipalFormation.at {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : PrincipalFormation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) :
    PrincipalAt (receipt.toFormation.code environment) (receipt.toFormation.support environment) :=
  .recaptured principal receipt.site receipt.expressionSyntax receipt.certificates receipt.body
    receipt.binderPolicy receipt.syntaxTree environment

/-- Actual producer selection and independently accepted same-Site body
receipts construct the ordinary certificate without choosing another head. -/
def ordinary_of_producer
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.Produced caller.named parameters result
      statements context evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source caller.named)
      (expressionSyntax (CallableIndexedNamedGeneration.source caller.named)) body.context
      (.statements true statements) result)
    (sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements produced.site.code.sourceNode.coercions [])
    (coercions : produced.site.code.sourceNode.coercions = []) :
    OrdinaryFormation (registry := registry) (faults := faults) caller context evidence scope id lowered where
  parameters := parameters
  result := result
  statements := statements
  site := produced.site
  expressionSyntax := expressionSyntax
  certificates := certificates
  body := body
  identifier := produced.identifier
  emitted := produced.emitted
  sourceType := sourceType
  ordinary := ordinary
  coercions := coercions
  binderPolicy := produced.binderPolicy
  syntaxTree := syntaxTree

/-- The principal certificate keeps its own Source dictionary and exact
producer seed, with independent full Syntax at that same body context. -/
def principal_of_producer {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.Produced principal.named parameters result
      statements context principal.dictionary scope (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source principal.named)
      (expressionSyntax (CallableIndexedNamedGeneration.source principal.named)) body.context
      (.statements true statements) result)
    (sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context principal.dictionary []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements produced.site.code.sourceNode.coercions [])
    (coercions : produced.site.code.sourceNode.coercions = []) :
    PrincipalFormation (registry := registry) (faults := faults) principal context scope id lowered where
  parameters := parameters
  result := result
  statements := statements
  site := produced.site
  expressionSyntax := expressionSyntax
  certificates := certificates
  body := body
  identifier := produced.identifier
  emitted := produced.emitted
  sourceType := sourceType
  ordinary := ordinary
  coercions := coercions
  binderPolicy := produced.binderPolicy
  syntaxTree := syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
