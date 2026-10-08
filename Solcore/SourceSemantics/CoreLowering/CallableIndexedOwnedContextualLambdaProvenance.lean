import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections

/-! Contextual provenance retains the original chosen Site, its real binder
policy and independent body Syntax. Constructor indices describe exactly the
existing recapture operation; no Site or Syntax is recovered from Code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The equation returned by the original contextual producer. -/
def BinderPolicy {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (named : CallableIndexedNamedGeneration.Named)
    (code : Code compiled.indexed function scope administrative) : Prop :=
  code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key []

/-- This is the same complete principal support record used at formation. -/
def principal_support {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
      context principal.dictionary [] scope administrative)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
      expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedMethodLambdaSupport.Support (recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment) registry faults where
  method := method
  principal := principal
  expressionSyntax := expressionSyntax
  certificates := certificates
  source := rfl
  compilation := site.compilation
  active := site.active
  body := recaptureBodyWith (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code body environment

/-- The actual ordinary seed and static body identify the exact recaptured
Code and Support. All Source fields remain those of the original seed. -/
inductive OrdinaryAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults → Prop where
  | recaptured
      (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
        context evidence [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
        expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults)
      (binderPolicy : BinderPolicy caller.named site.code)
      (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source caller.named)
        (expressionSyntax (CallableIndexedNamedGeneration.source caller.named)) body.context
        (.statements true statements) result)
      (environment : Dynamic.Environment) :
      OrdinaryAt (recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((CallableIndexedOwnedOrdinaryLambdaSupport.Support.of_site caller site expressionSyntax certificates body).recapture environment)

/-- The method seed keeps its own dictionary and principal, never an ordinary
Header. Its full body context and Syntax are indexed by the same chosen Site. -/
inductive PrincipalAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedMethodLambdaSupport.Support code registry faults → Prop where
  | recaptured {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
        context principal.dictionary [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
        expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults)
      (binderPolicy : BinderPolicy principal.named site.code)
      (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source principal.named)
        (expressionSyntax (CallableIndexedNamedGeneration.source principal.named)) body.context
        (.statements true statements) result)
      (environment : Dynamic.Environment) :
      PrincipalAt (recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        (principal_support principal site expressionSyntax certificates body environment)

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}

/-- Only proof goals consume the retained seed; no data Site is chosen from
the Prop receipt. Recapture preserves the exact policy definition. -/
theorem OrdinaryAt.binder_policy
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) : BinderPolicy support.caller.named code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy syntaxTree environment => exact binderPolicy

theorem OrdinaryAt.syntax
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
      support.body.context (.statements true function.body) function.resultType := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy syntaxTree environment => exact syntaxTree

theorem PrincipalAt.binder_policy
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) : BinderPolicy support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy syntaxTree environment => exact binderPolicy

theorem PrincipalAt.syntax
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
      support.body.context (.statements true function.body) function.resultType := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy syntaxTree environment => exact syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
