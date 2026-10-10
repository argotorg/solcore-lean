import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeads

/-! The concrete semantic domain retains the native-aware body generated at
one actual compiler lambda occurrence. The ordinary constructor keeps its real
Header membership; the Principal constructor keeps its actual selected method
and dictionary. Each body contains local raw child witnesses from the original
compiler traversal. Recapture retains that body and its literal Named prefix.
The original unrestricted or broad compiled qualifiers have no inverse here.
Finite raw Trees are constructed from these authentic child actions, while the
shared execution induction and concrete public static inputs remain open. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCollectedQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

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
inductive Principal : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
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
      (environment : Dynamic.Environment) :
      Principal
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) principal.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- Generic qualified payload and heap APIs use this one static facet. -/
def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := Ordinary headers
  principal := Principal

theorem ordinary_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual member root expressionSyntax certificate receipt environment =>
      exact .recaptured _ _ receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) _))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy environment

theorem principal_prepared
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support := by
  cases qualified with
  | actual principal root expressionSyntax certificate receipt environment =>
      exact .recaptured principal receipt.site expressionSyntax
        (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax («prefix» (compiled := compiled) principal.named))
        receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body receipt.binderPolicy environment

section Occurrence
variable {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {readFuel : Nat}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

/-- Forget only the local native witness to the original authentic compiler
action. This is a direct constructor projection, not a broad receipt inverse. -/
theorem accepted_action {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) sourceContext scope id lowered) :
    CallableIndexedOwnedPreparedPrincipalCompilerChildren.AcceptedAt root expressionSyntax
      readFuel (source named) sourceContext scope id lowered := by
  cases accepted with
  | intro found typed allowed declarations closed residual signatures action raw =>
      exact .intro found typed allowed declarations closed residual signatures action

/-- The actual compiler-fuel producer constructs the finite skeleton at this
retained child action. Its local native witness is kept at the exact same output;
unused Entries do not acquire typing. The later E fold consumes used slots only. -/
theorem tree_at_occurrence
    (domain : CallableIndexedOwnedPreparedRawCompilerHeads.Domain root expressionSyntax callerEvidence headers
      (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : CallableIndexedOwnedPreparedNativeCompilerChildren.AcceptedAt root expressionSyntax
      («prefix» (compiled := compiled) named) readFuel (source named) sourceContext scope id lowered) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence headers
        (sourceContext := sourceContext) (scope := scope))
      readFuel (.initial compiled.compatible.checked) (source named) sourceContext
      (context compiled.indexed named).solvedRequirements rootReasonAt scope id lowered ∧
      ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) named)
        lowered.expression nativeType compiled.indexed.layouts.definitions := by
  have tree := CallableIndexedOwnedPreparedRawCompilerHeads.tree_of_accepted root expressionSyntax
    callerEvidence headers domain unique (accepted_action root expressionSyntax accepted)
  refine ⟨tree, ?_⟩
  cases accepted with
  | intro found typed allowed declarations closed residual signatures action raw => exact ⟨_, raw⟩

end Occurrence
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCollectedQualification
