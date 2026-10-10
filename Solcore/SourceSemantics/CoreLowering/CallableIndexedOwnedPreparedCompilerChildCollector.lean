import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodySiteInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryBodyProjection

/-! Compiler-qualified ordinary bodies retain the actual selected formation
receipt and ChosenFactory before recapture. Their child certificates are the
original accepted compiler actions. The existing compiler induction constructs
one exact literal-supported expression Tree from each action; there is no
certificate-to-execution assumption. This finite ordinary/named/indirect static
collector does not classify arbitrary prepared Supports. A method collector
must retain its authentic Principal rather than manufacture an ordinary Header.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompilerChildCollector
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (Formation)
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {host : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed host.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) host.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

/-- This constructor is available only at the actual compiler-produced
Formation. Code, Support, JointBody and Source environment are copied from it.
In particular there is no constructor accepting a certificate equality. -/
inductive Collected : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    Support code → Prop where
  | formed {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt host diagnostics namedCode compilation
        context evidence scope id lowered)
      (chosen : ChosenFactory root expressionSyntax receipt)
      (environment : Dynamic.Environment) :
      Collected (receipt.formation.code environment) (receipt.formation.support environment)

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
  {support : Support code}

/-- The factory follows from the actual positive constructor, including the
exact original readFuel. It is never used as an inverse on old Supports. -/
theorem Collected.factories (collected : Collected root expressionSyntax code support) :
    support.expressionSyntax = expressionSyntax ∧ support.certificates = certificates root expressionSyntax := by
  cases collected with
  | formed receipt chosen environment =>
    have actual := recaptured_factory root expressionSyntax receipt chosen environment
    exact ⟨actual.1, actual.2.1⟩

theorem Collected.caller (collected : Collected root expressionSyntax code support) :
    support.caller = host := by
  cases collected with
  | formed receipt chosen environment => rfl

/-- Actual preparation remains attached to the same recaptured body. -/
theorem Collected.prepared (collected : Collected root expressionSyntax code support) :
    PreparedAt code support := by
  cases collected with
  | formed receipt chosen environment => exact receipt.formation.prepared environment

section Coverage
variable
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
  (domain : DomainAt root expressionSyntax support.body.readFuel currentContext function.evidence childScope headers)
  (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed host.named).solvedRequirements
    currentContext function.evidence)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) currentContext function.source)

include runtime

/-- Only static Source/context/scope/metadata and accepted lowering receipts
enter this collector. Actual named selection and Principal authority remain
separate. All runtime child meanings are supplied by the later grade induction.
The output has the original child id and lowered value, with no existential
replacement of the compiler's expression or ordered physical children. -/
theorem Collected.cover_for (supported : Bool)
    (collected : Collected root expressionSyntax code support)
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : support.certificates support.body.readFuel function.source currentContext childScope child output) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (CallsFor root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers supported)
      support.body.readFuel (.initial compiled.compatible.checked) (source host.named) currentContext
      (context compiled.indexed host.named).solvedRequirements rootReasonAt childScope child output := by
  cases collected with
  | formed receipt chosen environment =>
    exact support_cover_for root expressionSyntax receipt supported chosen environment headers domain valid runtime actual

/-- The public static endpoint selects the genuine supported mode, keeping
ordinary, named and indirect call heads and original literal-site receipts. -/
theorem Collected.cover
    (collected : Collected root expressionSyntax code support)
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : support.certificates support.body.readFuel function.source currentContext childScope child output) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (CallsFor root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers true)
      support.body.readFuel (.initial compiled.compatible.checked) (source host.named) currentContext
      (context compiled.indexed host.named).solvedRequirements rootReasonAt childScope child output :=
  Collected.cover_for root expressionSyntax headers domain valid runtime true collected actual

end Coverage
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompilerChildCollector
