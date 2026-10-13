import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes

/-! Full policy provenance follows the original selected producer Site through
ordinary or principal formation and exact recapture. Existing body receipts
remain the same static inputs. No policy is recovered from a body recipe. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaFormationReceipts
open CallableIndexedOwnedContextualLambdaProvenance

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : Named} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}

/-- Only the captured environment changes; all retained compiler fields are literal. -/
theorem retained_recapture {code : Code prepared function scope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named
      (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial checked) (indexed := prepared) code environment) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- An additional proof belongs to this existing ordinary Formation and Site. -/
structure OrdinaryWithPolicy
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends OrdinaryFormation (registry := registry) (faults := faults)
      caller context evidence scope id lowered where
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code

/-- Principal formation retains its own dictionary and selected policy. -/
structure PrincipalWithPolicy {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends PrincipalFormation (registry := registry) (faults := faults)
      principal context scope id lowered where
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code

/-- Ordinary provenance and policy refer to the same exact recaptured Code. -/
theorem OrdinaryWithPolicy.at
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryWithPolicy (registry := registry) (faults := faults)
      caller context evidence scope id lowered)
    (environment : Dynamic.Environment)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    OrdinaryAt (receipt.toOrdinaryFormation.toFormation.code environment)
      (receipt.toOrdinaryFormation.toFormation.support environment) ∧
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named
      (receipt.toOrdinaryFormation.toFormation.code environment) :=
  ⟨receipt.toOrdinaryFormation.at environment globals, retained_recapture receipt.policyRecipe environment⟩

/-- The method principal and all policy inputs survive this same recapture. -/
theorem PrincipalWithPolicy.at {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : PrincipalWithPolicy (registry := registry) (faults := faults)
      principal context scope id lowered)
    (environment : Dynamic.Environment) :
    PrincipalAt (receipt.toPrincipalFormation.toFormation.code environment)
      (receipt.toPrincipalFormation.toFormation.support environment) ∧
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named
      (receipt.toPrincipalFormation.toFormation.code environment) :=
  ⟨receipt.toPrincipalFormation.at environment, retained_recapture receipt.policyRecipe environment⟩

/-- Build the existing ordinary Formation from one actual ProducedWithPolicy.
Both its static BodyWith and retained policy belong to that original Site. -/
def ordinary_of_produced_with_policy
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.ProducedWithPolicy
      (compiled := compiled) caller.named parameters result statements context evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.produced.site.code
      (Program.ofChecked compiled.sourceProgram) registry faults)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.produced.site.code)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.produced.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
      (expressionSyntax (source caller.named)) body.context (.statements true statements) result)
    (sourceType : produced.produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.produced.site.code.sourceNode.requirements
      produced.produced.site.code.sourceNode.coercions [])
    (coercions : produced.produced.site.code.sourceNode.coercions = []) :
    OrdinaryWithPolicy (registry := registry) (faults := faults) caller context evidence scope id lowered where
  toOrdinaryFormation := ordinary_of_producer caller produced.produced expressionSyntax certificates body bodyView bodyReasons declarations
    syntaxTree sourceType ordinary coercions
  policyRecipe := produced.policyRecipe

/-- The same producer attachment preserves the actual method dictionary.
No ordinary Header, new Site or accepted-policy witness is selected. -/
def principal_of_produced_with_policy {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : CallableIndexedOwnedContextualLambdaProducerReceipts.ProducedWithPolicy
      (compiled := compiled) principal.named parameters result statements context principal.dictionary scope
      (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates produced.produced.site.code
      (Program.ofChecked compiled.sourceProgram) registry faults)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.produced.site.code)
    (syntaxTree : GenericImperativeMatch.Syntax (source principal.named)
      (expressionSyntax (source principal.named)) body.context (.statements true statements) result)
    (sourceType : produced.produced.site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure principal.named parameters result statements
        context principal.dictionary []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.produced.site.code.sourceNode.requirements
      produced.produced.site.code.sourceNode.coercions [])
    (coercions : produced.produced.site.code.sourceNode.coercions = []) :
    PrincipalWithPolicy (registry := registry) (faults := faults) principal context scope id lowered where
  toPrincipalFormation := principal_of_producer principal produced.produced expressionSyntax certificates body bodyView
    syntaxTree sourceType ordinary coercions
  policyRecipe := produced.policyRecipe

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyFormationReceipts
