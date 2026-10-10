import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeFamilyStaticQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSiteShellReceipts

/-! The final positive lambda qualification retains the actual selected
compiler issuance, the same selected shell issuer, and its literal receipt and occurrence factory. Ordinary
and method packets keep the same Site, body, dictionary and captured environment.
All adapters below are forward projections. A generic older compilation or
qualification supplies no selected issuer, receiving diagnostic identity, or
completed expression/body law. The finite occurrence and receiving factories
remain genuine static construction obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The ordinary constructor keeps the literal selected second-pass slot.
Its receipt and occurrence factory have that same compiler root. -/
inductive Ordinary (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop where
  | actual {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers) {index : Nat}
      (selected : SelectedReceipt compiled caller.named index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
      {statements : List StatementId} {reported : Ty} {childFuel : Nat}
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed caller.named) (source caller.named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (receipt : Receipt root expressionSyntax certificate (sourceContext := sourceContext) (evidence := evidence))
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Ordinary headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support.of_site
          caller selected.compilation receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) caller.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

/-- The method constructor retains the actual selector and selected receipt.
The support uses the positively reissued principal, with its full dictionary. -/
inductive Principal (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | actual {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (selected : SelectedReceipt compiled principal.named principal.cached.index)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
        selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
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
      (sameIssuer : receipt.shell.issued =
        CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site)
      (factory : OccurrenceFactory root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel)
      (environment : Dynamic.Environment) :
      Principal headers
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) receipt.site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site
          (SelectedReceipt.principal principal selected) receipt.site expressionSyntax
          (CallableIndexedOwnedPreparedNativeCompilerChildren.certificates root expressionSyntax
            («prefix» (compiled := compiled) principal.named))
          receipt.shell.issued receipt.shell.diagnosticPolicy receipt.body).recapture environment)

def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := Ordinary headers
  principal := Principal headers

theorem ordinary_family {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedNativeFamilyStaticQualification.Ordinary headers code support := by
  cases qualified with
  | actual member selected root expressionSyntax certificate receipt sameIssuer factory environment =>
      exact .actual member root expressionSyntax certificate receipt factory environment

theorem principal_family {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedNativeFamilyStaticQualification.Principal headers code support := by
  cases qualified with
  | actual principal selected root expressionSyntax certificate receipt sameIssuer factory environment =>
      exact .actual (SelectedReceipt.principal principal selected) root expressionSyntax certificate receipt factory environment

theorem ordinary_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.ordinary_prepared (ordinary_family qualified)

theorem principal_prepared {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.principal_prepared (principal_family qualified)

theorem ordinary_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
    (qualified : Ordinary headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Ordinary headers code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.ordinary_native (ordinary_family qualified)

theorem principal_native {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
    (qualified : Principal headers code support) :
    CallableIndexedOwnedPreparedNativeCollectedQualification.Principal code support :=
  CallableIndexedOwnedPreparedNativeFamilyStaticQualification.principal_native (principal_family qualified)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedNativeFamilyQualification
