import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes

/-! Contextual provenance retains the original chosen Site, its real binder
policy, production recipe and independent body Syntax. Constructor indices describe exactly the
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

/-- Metadata for every expression reached from the original body is retained
verbatim. Edits elsewhere in the source remain allowed. -/
def BodyView {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative) : Prop :=
  ∀ id, CallableLambdaBodyReachability.Reaches function.source
    (function.body.map NodeId.statement) (.expression id) →
    function.source.lookupExpression? id = code.view.lookupExpression? id

theorem BodyView.of_eq {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (same : code.view = function.source) : BodyView code := by
  intro id _reached
  rw [same]

theorem BodyView.of_empty {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (empty : function.body = []) : BodyView code := by
  intro id reached
  have none {node : NodeId} (path : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) node) : False := by
    induction path with
    | root member => simp only [empty, List.map_nil, List.not_mem_nil] at member
    | expression _ _ _ ih => exact ih
    | statement _ _ _ ih => exact ih
  exact False.elim (none reached)

/-- Reached reads keep the original token from the compiler's actual issuer. -/
def BodyReasons {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative)
    (named : CallableIndexedNamedGeneration.Named) : Prop :=
  ∀ id, CallableLambdaBodyReachability.Reaches function.source
    (function.body.map NodeId.statement) (.expression id) →
    ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some diagnostics ∧
      code.reasonAt id = diagnostics.program.reasonAt named.signature.key id

theorem BodyReasons.of_issued {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (issued : compiled.indexed.base.diagnostics = some diagnostics)
    (same : code.reasonAt = diagnostics.program.reasonAt named.signature.key) : BodyReasons code named := by
  intro id _reached
  exact ⟨diagnostics, issued, congrFun same id⟩

theorem BodyReasons.of_empty {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named} (empty : function.body = []) : BodyReasons code named := by
  intro id reached
  have none {node : NodeId} (path : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) node) : False := by
    induction path with
    | root member => simp only [empty, List.map_nil, List.not_mem_nil] at member
    | expression _ _ _ ih => exact ih
    | statement _ _ _ ih => exact ih
  exact False.elim (none reached)

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
      (recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained caller.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code)
      (bodyView : BodyView site.code)
      (bodyReasons : BodyReasons site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations
        (CallableIndexedNamedGeneration.source caller.named) scope context)
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
      (recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained principal.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code)
      (bodyView : BodyView site.code)
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
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView bodyReasons declarations syntaxTree environment => exact binderPolicy

theorem OrdinaryAt.syntax
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
      support.body.context (.statements true function.body) function.resultType := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView bodyReasons declarations syntaxTree environment => exact syntaxTree

theorem PrincipalAt.binder_policy
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) : BinderPolicy support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView syntaxTree environment => exact binderPolicy

theorem PrincipalAt.syntax
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
      support.body.context (.statements true function.body) function.resultType := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView syntaxTree environment => exact syntaxTree

/-- The same original production recipe survives recapture at the ordinary seed. -/
theorem OrdinaryAt.body_recipe
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView bodyReasons declarations syntaxTree environment =>
      exact recipe

/-- Method provenance retains its own principal and the same production recipe. -/
theorem PrincipalAt.body_recipe
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView syntaxTree environment =>
      exact recipe

/-- The original actual expression policy remains attached to this same Code
when captures are installed. It is not recovered from body compilation. -/
theorem OrdinaryAt.policy_recipe
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView bodyReasons declarations syntaxTree environment =>
      exact compilerPolicy

theorem PrincipalAt.policy_recipe
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.principal.named code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView syntaxTree environment =>
      exact compilerPolicy

/-- Recapture preserves the exact original body lookups. -/
theorem OrdinaryAt.body_view
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) : BodyView code := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView bodyReasons declarations syntaxTree environment =>
      exact bodyView

/-- Recapture retains the original named diagnostic tokens on all used reads. -/
theorem OrdinaryAt.body_reasons
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) : BodyReasons code support.caller.named := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView bodyReasons declarations syntaxTree environment =>
      exact bodyReasons

/-- The captured scope retains its original Source binder declarations. -/
theorem OrdinaryAt.scope_declarations
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (receipt : OrdinaryAt code support) :
    CompatibleExpressionReads.ScopeDeclarations function.source scope function.context := by
  cases receipt with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView bodyReasons declarations syntaxTree environment =>
      exact declarations

theorem PrincipalAt.body_view
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (receipt : PrincipalAt code support) : BodyView code := by
  cases receipt with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy bodyView syntaxTree environment =>
      exact bodyView

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
