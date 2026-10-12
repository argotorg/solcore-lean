import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads

/-! Each actual raw lambda branch and its genuine fixed-prefix native witness
construct one tagged compiler Receipt, then retain the occurrence factory for
THAT receipt's body read fuel. The same accepted Certificate/action/Source row
is forwarded to the positive runtime lambda leaf. Ordinary and Principal roots
keep their actual caller identity and full dictionary.

The Source body receipt and finite compiler occurrence factory are static
inputs. No Tree, expression execution, application, or body law is accepted. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts (SelectedReceipt lowered)
open CallableIndexedOwnedPreparedNativeSiteShellReceipts (FiniteBodyReceipts)
open CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedNativeFamilyStaticQualification (OccurrenceFactory)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

namespace Ordinary
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)} {index : Nat}
  (selected : SelectedReceipt compiled caller.named index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {scope : SourceCoreLocalCell.Scope}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source caller.named))
  (covers : evidence.Covers context)
  (ownership : LocalIdentityOwnership (source caller.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
  (sameReason : rootReasonAt = selected.diagnostics.program.reasonAt caller.named.signature.key)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements)

include profile runtime covers ownership declarations sameReason sameLedger in
/-- The compiler creates the Receipt once. The static factory is selected only
at that literal generated Receipt and exact selected issuer identity. -/
theorem of_compiler {children : GenericExpressionMeaning.Certificate}
    {childFuel id lowered node parameters result statements reported nativeType}
    (allowed : expressionSyntax (source caller.named) id)
    (found : (source caller.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered)
    (sourceTyped : ExpressionHasType (source caller.named) context id node.type)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source caller.named) id node lowered.type)
    (coercions : node.coercions = [])
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) caller.named)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source caller.named) (expressionSyntax (source caller.named)) context parameters result statements)
    (occurrences : ∀ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := evidence),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
      OccurrenceFactory root expressionSyntax (some evidence) headers receipt.body.readFuel) :
    CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.Lambdas selected root expressionSyntax headers
      (context := context) (evidence := evidence) (scope := scope) children scope id lowered := by
  obtain ⟨receipt, sameIssuer⟩ := CallableIndexedOwnedPreparedSelectedPositiveOrdinaryLambdaHeads.compiler_receipt
    selected root expressionSyntax profile runtime covers ownership declarations sameLedger
    certificate found form sourceTyped coercions accepted raw finite
  exact .actual allowed found form certificate accepted sourceTyped metadata raw finite
    receipt (CallableIndexedOwnedContextualLambdaProvenance.BodyReasons.of_issued selected.found
      (receipt.reason.trans sameReason)) declarations sameIssuer (occurrences receipt sameIssuer)
end Ordinary

namespace Principal
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (selected : SelectedReceipt compiled principal.named principal.cached.index)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) principal.named (lowered compiled selected.diagnostics)
    selected.code selected.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (source principal.named))
  (covers : principal.dictionary.Covers context)
  (ownership : LocalIdentityOwnership (source principal.named))
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source principal.named) scope context)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed principal.named).solvedRequirements)

include profile runtime covers ownership declarations sameLedger in
/-- The compiler creates the Receipt once. The static factory is selected only
at that literal generated Receipt and exact selected issuer identity. -/
theorem of_compiler {children : GenericExpressionMeaning.Certificate}
    {childFuel id lowered node parameters result statements reported nativeType}
    (allowed : expressionSyntax (source principal.named) id)
    (found : (source principal.named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope
      id node parameters result statements reported rootReasonAt lowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (CallableIndexedNamedGeneration.context compiled.indexed principal.named) (source principal.named) scope id rootReasonAt = .ok lowered)
    (sourceTyped : ExpressionHasType (source principal.named) context id node.type)
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source principal.named) id node lowered.type)
    (coercions : node.coercions = [])
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) principal.named)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (finite : FiniteBodyReceipts (source principal.named) (expressionSyntax (source principal.named)) context parameters result statements)
    (occurrences : ∀ receipt : Receipt root expressionSyntax certificate (sourceContext := context) (evidence := principal.dictionary),
      receipt.shell.issued = CallableIndexedOwnedPreparedNativeSiteShellReceipts.issued_at_site selected receipt.site →
      OccurrenceFactory root expressionSyntax (some principal.dictionary) headers receipt.body.readFuel) :
    CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.Lambdas principal selected root expressionSyntax headers
      (context := context) (scope := scope) children scope id lowered := by
  obtain ⟨receipt, sameIssuer⟩ := CallableIndexedOwnedPreparedSelectedPositivePrincipalLambdaHeads.compiler_receipt
    principal selected root expressionSyntax profile runtime covers ownership declarations sameLedger
    certificate found form sourceTyped coercions accepted raw finite
  exact .actual allowed found form certificate accepted sourceTyped metadata raw finite
    receipt sameIssuer (occurrences receipt sameIssuer)
end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedPositiveLambdaPackets
