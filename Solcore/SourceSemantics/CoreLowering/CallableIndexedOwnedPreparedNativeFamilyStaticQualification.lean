import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCollectedQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds

/-! Intermediate static qualification for the one collected family. Each
retained compiler occurrence supplies the original finite raw Domain at its
actual context/scope/read fuel. The original finite producer constructs the
same Tree; its own raw native witness is paired with that Tree.

No field stores a Tree, an expression meaning or a body execution law. The
actual compiler must still manufacture these static Domain packets for every
supported evidence/coercion/generalized alternative. Existing broad native
qualification has only a forward projection from this stronger domain. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyStaticQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

section Factory
variable {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  (readFuel : Nat)

/-- The input is the literal retained AcceptedAt, including its independent
Source facts and raw native witness. Domain carries only finite compiler facts;
its empty/coercion restrictions are not conclusions of ProgramWellFormed. -/
structure OccurrenceFactory : Prop where
  domain : ∀ {currentContext currentScope id lowered},
    CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) currentContext currentScope id lowered →
    CallableIndexedOwnedPreparedRawCompilerHeads.Domain root expressionSyntax callerEvidence headers
      (sourceContext := currentContext) (scope := currentScope) (readFuel := readFuel)

/-- One genuine finite compiler-fuel construction at the SAME accepted child.
The native witness is its own retained witness; unused child slots gain none. -/
theorem OccurrenceFactory.runtime_tree
    (factory : OccurrenceFactory root expressionSyntax callerEvidence headers readFuel)
    (unique : NodeOccurrencesUnique (source named))
    {currentContext currentScope id lowered}
    (accepted : CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) currentContext currentScope id lowered) :
    CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := currentContext) (compilerScope := currentScope) (fuel := readFuel)
      (solved := (context compiled.indexed named).solvedRequirements)
      root expressionSyntax callerEvidence headers («prefix» (compiled := compiled) named)
      currentScope id lowered := by
  obtain ⟨tree, raw⟩ := CallableIndexedOwnedPreparedNativeCollectedQualification.tree_at_occurrence
    root expressionSyntax callerEvidence headers (factory.domain accepted) unique accepted
  exact ⟨tree, raw⟩
end Factory

/-- The only ordinary leaf is the same positive compiler Receipt, body and
recaptured environment. Actual Header membership remains explicit. -/
inductive Ordinary (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop where
  | actual {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers)
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
      {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
        rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
      {statements : List StatementId} {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := sourceContext) (evidence := evidence))
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons receipt.site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations
        (source caller.named) scope sourceContext)
      (factory : OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Ordinary headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
          caller compilation receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) caller.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- The method leaf retains its full selector and literal dictionary. No
ordinary Header or arbitrary administrative-context equality is constructed. -/
inductive Principal (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | actual {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
        principal.cached.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
      {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed principal.named) (source principal.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate
        (sourceContext := sourceContext) (evidence := principal.dictionary))
      (factory : OccurrenceFactory root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Principal headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) principal.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- Generic qualified payload and heap APIs use this one static facet. -/
def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := Ordinary headers
  principal := Principal headers

theorem ordinary_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual member root expressionSyntax certificate receipt bodyReasons declarations factory environment =>
      exact .recaptured _ _ receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) _))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy
        (by
          have policy := root.compilerPolicy
          rw [← receipt.policy] at policy
          exact CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes _
            (receipt.lowerBody.trans root.selected.recipe) policy receipt.site.compilation)
        (receipt.issued_recipe root expressionSyntax certificate)
        (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq receipt.view) bodyReasons declarations environment

theorem principal_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual principal root expressionSyntax certificate receipt factory environment =>
      exact .recaptured principal receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) principal.named))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy
        (by
          have policy := root.compilerPolicy
          rw [← receipt.policy] at policy
          exact CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes _
            (receipt.lowerBody.trans root.selected.recipe) policy receipt.site.compilation)
        (receipt.issued_recipe root expressionSyntax certificate)
        (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq receipt.view) environment

/-- Forward compiler qualification preserves exactly the same Code/body.
There is no projection back from the broad native facet. -/
theorem ordinary_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Ordinary headers code support := by
  cases qualified with
  | actual member root expressionSyntax certificate receipt bodyReasons declarations factory environment =>
      exact .actual member root expressionSyntax certificate receipt bodyReasons declarations environment

theorem principal_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Principal code support := by
  cases qualified with
  | actual principal root expressionSyntax certificate receipt factory environment =>
      exact .actual principal root expressionSyntax certificate receipt environment

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyStaticQualification
